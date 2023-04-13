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


open import Arch.Mixed as Mixed using (MixedExecution)


module Relations {ex : Execution {arch-x86}} (xex : MixedExecution ex) where

  open Π.Defs ex
  open MixedExecution xex


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
    --
    -- Note that skips are an artifact of our proof structure, representing NOPs.
    -- Skips are not ordered with anything.
    lob-po : ( po-no-skip \₂ (⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvR ⦘) ) x y → Lobi x y
    -- this was previously (in `implied`):
    -- ( po ⨾ ⦗ EvF ⦘ ) ∪₂ ( ⦗ EvF ⦘ ⨾ po )
    -- which was *stronger* (in isolation, at least). this current form is weaker.
    lob-f  : ( ⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvF ⦘ ⨾ po ⨾ ⦗ EvR ⦘ ) x y → Lobi x y
    -- The "official" mixed-size model states:
    -- `⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvRₐ ⦘`
    -- while the non-mixed-size model states:
    -- `po ⨾ ⦗ dom rmw ⦘`
    -- The former also holds for *failed RMWs*, while the latter does not. It is thus
    -- stronger (i.e., it applies to fewer cases), making the model weaker (i.e., more
    -- cycles are allowed). However, this new definition is problematic, as it does not
    -- hold in Armv8. Hence, it seems like a poor design decision. So, we stick with the
    -- old definition.
    --
    -- Actually, this rule is now redundant. (See `Proof.X86toTCG.Consistent`)
    lob-rmwˡ : ( ⦗ EvW ⦘ ⨾ po ⨾ ⦗ dom rmw ⦘ )  x y → Lobi x y
    -- this one is just framed differently from: `⦗ codom rmw ⦘ ⨾ po`, as we know that
    -- `⦗ codom rmw ⦘ ≡ EvWₐ`. (i.e., RMW can only fail their write. The RMW was successful
    --   iff the write event exists)
    lob-rmwʳ : ( ⦗ codom rmw ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → Lobi x y

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
