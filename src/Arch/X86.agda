{-# OPTIONS --safe #-}

-- | x86 mixed-size model, taken from:
-- https://github.com/herd/herdtools7/blob/master/herd/libdir/x86tso-mixed.cat
--
-- It changes quite a bit from its previous non-mixed version. Though, many of
-- those changes are merely refactorings; Which don't change semantics.
module Arch.X86 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_; flip)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to ⊎[_,_])
open import Data.Product using (_,_; ∃-syntax)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty)
open import Relation.Binary using (Rel; Irreflexive; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
open import Burrow.Template.Arch as Π
-- Local imports
open import Helpers


-- # Definitions

data LabR : Set where
  lab-r : Tag → LabR

data LabW : Set where
  lab-w : Tag → LabW

data LabF : Set where
  lab-f : LabF

lab-r-tag : LabR → Tag
lab-r-tag (lab-r tag) = tag

lab-w-tag : LabW → Tag
lab-w-tag (lab-w tag) = tag

lab-r-dec≡ : Dec≡ LabR
lab-r-dec≡ (lab-r t₁) (lab-r t₂) = cong-dec lab-r (λ{refl → refl}) (tag-dec≡ t₁ t₂)

lab-w-dec≡ : Dec≡ LabW
lab-w-dec≡ (lab-w t₁) (lab-w t₂) = cong-dec lab-w (λ{refl → refl}) (tag-dec≡ t₁ t₂)

lab-f-dec≡ : Dec≡ LabF
lab-f-dec≡ lab-f lab-f = yes refl

arch-x86 : Arch
arch-x86 =
  record
    { LabR       = LabR
    ; LabW       = LabW
    ; LabF       = LabF
    ; lab-r-tag  = lab-r-tag
    ; lab-w-tag  = lab-w-tag
    ; lab-r-dec≡ = lab-r-dec≡
    ; lab-w-dec≡ = lab-w-dec≡
    ; lab-f-dec≡ = lab-f-dec≡
    }

open Π.Ev arch-x86

EventX86 = Event -- note that this is parametrized over `arch-x86`

record X86Execution (ex : Execution {arch-x86}) : Set₁ where
  open Execution ex
  field
    si : Rel₀ Event

    -- # X86-specific wellformedness axioms

    si-internal : si ⊆₂ (po ∪₂ flip po ∪₂ ⦗ events ⦘)
    -- basically, `si` is an equivalence.
    -- note that the `filter-rel events` is crucial here. otherwise we can prove
    -- false. pick an `x` ∉ events, construct `si x x`, construct `po x x` (with
    -- `si-internal`), construct `x ∈ events` (with `po-elements`). tada, ⊥.
    si-refl  : Reflexive (filter-rel events si)
    si-trans : Transitive si
    si-sym   : Symmetric si


module Relations {ex : Execution {arch-x86}} (xex : X86Execution ex) where

  open Π.Defs ex
  open X86Execution xex


  -- | Coherence after
  data Ca (x y : Event) : Set where
    ca-fr : fr x y → Ca x y
    ca-co : co x y → Ca x y

  -- | Observed-by
  data Obs (x y : Event) : Set where
    obs-rfe : rfe x y → Obs x y
    obs-fre : fre x y → Obs x y
    obs-coe : coe x y → Obs x y

  -- | Immediate Locally ordered before
  --
  -- This contains several cases of what previously was:
  -- * xppo (X86 Happens Before) - became `lob-po`
  -- * implied - became lob-f, lob-rₐ, and lob-wₐ
  --     (with subtle changes, see those constructors)
  data Lobi (x y : Event) : Set where
    -- this was previously `xppo`
    lob-po : ( po \₂ (⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvR ⦘) ) x y → Lobi x y
    -- this was previously (in `implied`):
    -- ( po ⨾ ⦗ EvF ⦘ ) ∪₂ ( ⦗ EvF ⦘ ⨾ po )
    -- which was *stronger* (in isolation, at least). this current form is weaker.
    lob-f  : ( ⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvF ⦘ ⨾ po ⨾ ⦗ EvR ⦘ ) x y → Lobi x y
    -- this was previously weaker: `po ⨾ ⦗ dom rmw ⦘`. the current variant also holds
    -- for *failed RMWs*.
    -- (i.e., definition got weaker, axiom `ax-external` restricts more, so model got stronger)
    lob-rₐ : ( ⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvRₐ ⦘ )  x y → Lobi x y
    -- this one is just framed differently from: `⦗ codom rmw ⦘ ⨾ po`, as we know that
    -- `⦗ codom rmw ⦘ ≡ EvWₐ`. (i.e., RMW can only fail their write. The RMW was successful
    --   iff the write event exists)
    lob-wₐ : ( ⦗ EvWₐ ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → Lobi x y

  -- | Locally-ordered-before
  lob : Rel₀ Event
  lob = TransClosure Lobi

  -- | Immediate Ordered-before
  --
  -- This replaces what previously was `xhb` (X86 Happens before). The `lob` case
  -- contains many of its cases, except `rfe`, `fr`, and `co`. The `obs` case
  -- contains `rfe`, `fre`, and `coe`. That leaves `fri` and `coi` unaccounted
  -- for. However, as `fri ⊆ R × W` and `coi ⊆ W × W`, they are included in
  -- `Lobi` in the `lob-po` constructor.
  data Obi (x y : Event) : Set where
    ob-obs : ( Obs ⨾ si ) x y → Obi x y
    ob-lob : lob          x y → Obi x y

  -- | Ordered-before
  ob : Rel₀ Event
  ob = TransClosure Obi
  

  record IsX86Consistent : Set where
    field
      ax-internal   : Acyclic _≡_ ( po-loc ∪₂ Ca ∪₂ rf )
      ax-atomicity  : Empty₂ (rmw ∩₂ (fre ⨾ coe))
      ax-external   : Irreflexive _≡_ ob


module Properties {ex : Execution {arch-x86}}
  (xex : X86Execution ex)
  (wf : WellFormed ex)
  where
  
  open Relations xex
  open Π.Defs ex
  open Π.WfDefs wf
  open X86Execution xex

  si-elements : udr si ⇔₁ events
  si-elements = ⇔: proof-⊆ proof-⊇
    where
    proof-⊆ : udr si ⊆₁' events
    proof-⊆ x (opt₁ (y , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poˡ∈ex po[xy]
    ... | opt₂ po[yx] = poʳ∈ex po[yx]
    ... | opf₃ (refl , x∈src) = x∈src
    proof-⊆ y (opf₂ (x , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poʳ∈ex po[xy]
    ... | opt₂ po[yx] = poˡ∈ex po[yx]
    ... | opf₃ (refl , x∈src) = x∈src

    proof-⊇ : events ⊆₁' udr si
    proof-⊇ x x∈ex =
      let si[xx] = si-refl {with-pred x x∈ex}
      in opt₁ (x , si[xx])

  siˡ∈ex : si ˡ∈ex
  siˡ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₁ ∘ (_ ,_)

  siʳ∈ex : si ʳ∈ex
  siʳ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₂ ∘ (_ ,_)
