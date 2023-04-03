{-# OPTIONS --safe #-}


module Arch.TCG where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Function using (_∘_; flip)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂; swap) renaming ([_,_] to ⊎[_,_])
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty; _∈_)
open import Relation.Binary using (Rel; Irreflexive; Reflexive; Transitive; Symmetric; IsEquivalence)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary hiding (REL)
open import Burrow.Template.Arch as Π
-- Local imports
open import Helpers


data LabR : Set where
  lab-r : Tag → LabR

data LabW : Set where
  lab-w : Tag → LabW


-- | Classifier for memory accesses. Used in `LabF`.
data AccessClass : Set where
  𝐴R : AccessClass -- read
  𝐴W : AccessClass -- write
  𝐴M : AccessClass -- memory (read / write)


-- | Fence mode. (See `lab-f` in `LabelTCG`)
--
-- Naming conventions:
-- * R  =  Read
-- * W  =  Write
-- * M  =  Memory  = Read / Write
data LabF : Set where
  -- | Orders two classes of accesses
  --
  -- Example:
  -- > 𝐴R 𝐹 𝐴W
  -- represents a fence ordering *preceding reads* with *subsequent writes*.
  _𝐹_ : AccessClass → AccessClass → LabF


-- # Lemmas/Properties

lab-r-tag : LabR → Tag
lab-r-tag (lab-r tag) = tag

lab-w-tag : LabW → Tag
lab-w-tag (lab-w tag) = tag

lab-r-dec≡ : Dec≡ LabR
lab-r-dec≡ (lab-r t₁) (lab-r t₂) = cong-dec lab-r (λ{refl → refl}) (tag-dec≡ t₁ t₂)

lab-w-dec≡ : Dec≡ LabW
lab-w-dec≡ (lab-w t₁) (lab-w t₂) = cong-dec lab-w (λ{refl → refl}) (tag-dec≡ t₁ t₂)

access-class-dec≡ : Dec≡ AccessClass
access-class-dec≡ 𝐴R 𝐴R = yes refl
access-class-dec≡ 𝐴W 𝐴W = yes refl
access-class-dec≡ 𝐴M 𝐴M = yes refl
access-class-dec≡ 𝐴R 𝐴W = no (λ())
access-class-dec≡ 𝐴R 𝐴M = no (λ())
access-class-dec≡ 𝐴W 𝐴R = no (λ())
access-class-dec≡ 𝐴W 𝐴M = no (λ())
access-class-dec≡ 𝐴M 𝐴R = no (λ())
access-class-dec≡ 𝐴M 𝐴W = no (λ())

lab-f-dec≡ : Dec≡ LabF
lab-f-dec≡ (l₁ 𝐹 r₁) (l₂ 𝐹 r₂) =
  cong₂-dec _𝐹_
    (λ{refl → refl}) (λ{refl → refl})
    (access-class-dec≡ l₁ l₂) (access-class-dec≡ r₁ r₂)

arch-TCG : Arch
arch-TCG =
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

pattern RR = 𝐴R 𝐹 𝐴R
pattern RW = 𝐴R 𝐹 𝐴W
pattern RM = 𝐴R 𝐹 𝐴M
pattern WR = 𝐴W 𝐹 𝐴R
pattern WW = 𝐴W 𝐹 𝐴W
pattern WM = 𝐴W 𝐹 𝐴M
pattern MR = 𝐴M 𝐹 𝐴R
pattern MW = 𝐴M 𝐹 𝐴W
pattern MM = 𝐴M 𝐹 𝐴M

pattern M? = 𝐴M 𝐹 _


open Π.Ev arch-TCG

EventTCG = Event -- note that this is parameterized over `arch-TCG`


record TCGExecution (ex : Execution {arch-TCG}) : Set₁ where
  open Execution ex
  field
    -- # Definitions
    
    si : Rel₀ Event -- ^ Same Instruction relation


    -- # Wellformedness

    si-internal : si ⊆₂ (po ∪₂ flip po ∪₂ ⦗ events ⦘)
    -- basically, `si` is an equivalence relation.
    -- note that the `filter-rel events` is crucial here. otherwise we can prove
    -- false. pick an `x` ∉ events, construct `si x x`, construct `po x x` (with
    -- `si-internal`), construct `x ∈ events` (with `po-elements`). tada, ⊥.
    si-refl  : Reflexive (filter-rel events si)
    si-trans : Transitive si
    si-sym   : Symmetric si
    
module Relations {ex : Execution {arch-TCG}} (tex : TCGExecution ex) where

  open Π.Defs ex
  open TCGExecution tex


  -- | Events ordered across the program order (po).
  --
  --
  -- # Design Decision: Not Union Representation
  --
  -- Consider this the union over all relations in it's constructors.
  --
  -- This data structure is much easier to handle than taking _∪₂_ over all these,
  -- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
  data Ord (x y : Event) : Set where
    ord-init      : ( ⦗ EvInit ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y

    -- memory fences

    ord-rr        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → Ord x y
    ord-rw        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → Ord x y
    ord-rm        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y

    ord-wr        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → Ord x y
    ord-ww        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → Ord x y
    ord-wm        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y

    ord-mr        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → Ord x y
    ord-mw        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → Ord x y
    ord-mm        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y


    -- other ordering operations

    -- ord-rmw-dom   : ( po ⨾ ⦗ dom rmw ⦘ )   x y → Ord x y
    ord-rmw-codom : ( ⦗ codom rmw ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y

    ord-w         : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvWₐ ⦘ ) x y → Ord x y
    ord-r         : ( ⦗ EvRₐ ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → Ord x y


  -- | Immediate global happens before. (See `ghb` below)
  data Ghbi (x y : Event) : Set where
    ghbi-ord : Ord x y → Ghbi x y
    -- these three cases are the same as the new Arm case `Obs ⨾ si`
    ghbi-rfe : ( rfe ⨾ si ) x y → Ghbi x y
    ghbi-coe : ( coe ⨾ si ) x y → Ghbi x y
    ghbi-fre : ( fre ⨾ si ) x y → Ghbi x y

  -- | Coherence
  data Coh (x y : Event) : Set where
    coh-po-loc : po-loc x y → Coh x y
    coh-rf     : rf     x y → Coh x y
    coh-fr     : fr     x y → Coh x y
    coh-co     : co     x y → Coh x y


  -- | Global happens before
  ghb : Rel₀ Event
  ghb = TransClosure Ghbi


  record IsTCGConsistent : Set where
    field
      -- # TCG-specific consistency constraints

      ax-coherence  : Acyclic _≡_ Coh
      ax-atomicity  : Empty₂ (rmw ∩₂ (fre ⨾ coe))
      ax-global-ord : Irreflexive _≡_ ghb


module Properties {ex : Execution {arch-TCG}}
  (tex : TCGExecution ex)
  (wf : WellFormed ex)
  where

  open Relations tex
  open Π.Defs ex
  open Π.WfDefs wf
  open TCGExecution tex


  si-elements : udr si ⇔₁ events
  si-elements = ⇔: proof-⊆ proof-⊇
    where
    proof-⊆ : udr si ⊆₁' events
    proof-⊆ x (opt₁ (y , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poˡ∈ex po[xy]
    ... | opt₂ po[yx] = poʳ∈ex po[yx]
    ... | opf₃ (_ , x∈ex) = x∈ex
    proof-⊆ y (opf₂ (x , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poʳ∈ex po[xy]
    ... | opt₂ po[yx] = poˡ∈ex po[yx]
    ... | opf₃ (refl , x∈ex) = x∈ex

    proof-⊇ : events ⊆₁' udr si
    proof-⊇ x x∈ex =
      let si[xx] = si-refl {with-pred x x∈ex}
      in opt₁ (x , si[xx])

  siˡ∈ex : si ˡ∈ex
  siˡ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₁ ∘ (_ ,_)
  
  siʳ∈ex : si ʳ∈ex
  siʳ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₂ ∘ (_ ,_)
  

  coh-irreflexive : Irreflexive _≡_ Coh
  coh-irreflexive refl (coh-po-loc (po[xx] , _)) = po-irreflexive refl po[xx]
  coh-irreflexive refl (coh-rf rf[xx])           = rf-irreflexive refl rf[xx]
  coh-irreflexive refl (coh-fr fr[xx])           = fr-irreflexive refl fr[xx]
  coh-irreflexive refl (coh-co co[xx])           = co-irreflexive refl co[xx]

  cohˡ∈ex : Coh ˡ∈ex
  cohˡ∈ex (coh-po-loc po-loc[xy]) = poˡ∈ex (proj₁ po-loc[xy])
  cohˡ∈ex (coh-rf rf[xy])         = rfˡ∈ex rf[xy]
  cohˡ∈ex (coh-fr fr[xy])         = frˡ∈ex fr[xy]
  cohˡ∈ex (coh-co co[xy])         = coˡ∈ex co[xy]


  ord-f⇒po :
    ∀ {p₁ : Pred₀ Event}
    → {f : LabF}
    → {p₂ : Pred₀ Event}
    → {x y : Event}
    → (⦗ p₁ ⦘ ⨾ po ⨾ ⦗ EvFₜ f ⦘ ⨾ po ⨾ ⦗ p₂ ⦘) x y
      --------------------------------------------
    → po x y
  ord-f⇒po ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
    po-trans po[xz] po[zy]


  ord⇒po :
      {x y : Event}
    → Ord x y
      -------------
    → po x y
  ord⇒po (ord-init ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
  ord⇒po (ord-rr rr[xy]) = ord-f⇒po rr[xy]
  ord⇒po (ord-rw rw[xy]) = ord-f⇒po rw[xy]
  ord⇒po (ord-rm rm[xy]) = ord-f⇒po rm[xy]
  ord⇒po (ord-wr rw[xy]) = ord-f⇒po rw[xy]
  ord⇒po (ord-ww ww[xy]) = ord-f⇒po ww[xy]
  ord⇒po (ord-wm wm[xy]) = ord-f⇒po wm[xy]
  ord⇒po (ord-mr mr[xy]) = ord-f⇒po mr[xy]
  ord⇒po (ord-mw mw[xy]) = ord-f⇒po mw[xy]
  ord⇒po (ord-mm mm[xy]) = ord-f⇒po mm[xy]
  ord⇒po (ord-rmw-codom ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
  ord⇒po (ord-w ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _)))         = po[xy]
  ord⇒po (ord-r ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _)))         = po[xy]

  ord⁺⇒po : {x y : Event} → TransClosure Ord x y → po x y
  ord⁺⇒po = ⁺-join-trans po-trans ∘ (⁺-map (λ τ → τ) ord⇒po)

  ord-predˡ : {x y : Event}
    → {P Q R : Pred₀ Event}
    → ( ⦗ P ⦘ ⨾ po ⨾ ⦗ Q ⦘ ⨾ po ⨾ ⦗ R ⦘ ) x y
      ---------------------------------------
    → P x
  ord-predˡ ((refl , Px) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) = Px

  ord-predʳ : {x y : Event}
    → {P Q R : Pred₀ Event}
    → ( ⦗ P ⦘ ⨾ po ⨾ ⦗ Q ⦘ ⨾ po ⨾ ⦗ R ⦘ ) x y
      ---------------------------------------
    → R y
  ord-predʳ ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , Ry)) = Ry


  ord-irreflexive : Irreflexive _≡_ Ord
  ord-irreflexive refl = po-irreflexive refl ∘ ord⇒po

  -- ghbi-irreflexive : Irreflexive _≡_ Ghbi
  -- ghbi-irreflexive refl (ghbi-ord ord[xx]) = ord-irreflexive refl ord[xx]
  -- ghbi-irreflexive refl (ghbi-rfe (rfe[xy] ⨾[ _ ]⨾ si[yx])) =
  --   proj₂ rfe[xy] (swap (⊆₂-apply si-internal si[yx]))
  -- ghbi-irreflexive refl (ghbi-coe (coe[xy] ⨾[ _ ]⨾ si[yx])) =
  --   proj₂ coe[xy] (swap (⊆₂-apply si-internal si[yx]))
  -- ghbi-irreflexive refl (ghbi-fre (fre[xy] ⨾[ _ ]⨾ si[yx])) =
  --   proj₂ fre[xy] (swap (⊆₂-apply si-internal si[yx]))


  ordˡ∈ex : Ord ˡ∈ex
  ordˡ∈ex = poˡ∈ex ∘ ord⇒po

  ordʳ∈ex : Ord ʳ∈ex
  ordʳ∈ex = poʳ∈ex ∘ ord⇒po


  ghbiˡ∈ex : Ghbi ˡ∈ex
  ghbiˡ∈ex (ghbi-ord ord[xy]) = ordˡ∈ex ord[xy]
  ghbiˡ∈ex (ghbi-rfe (rfe[xy] ⨾[ _ ]⨾ _)) = rfˡ∈ex (proj₁ rfe[xy])
  ghbiˡ∈ex (ghbi-coe (coe[xy] ⨾[ _ ]⨾ _)) = coˡ∈ex (proj₁ coe[xy])
  ghbiˡ∈ex (ghbi-fre (fre[xy] ⨾[ _ ]⨾ _)) = frˡ∈ex (proj₁ fre[xy])

  ghbiʳ∈ex : Ghbi ʳ∈ex
  ghbiʳ∈ex (ghbi-ord ord[xy]) = ordʳ∈ex ord[xy]
  ghbiʳ∈ex (ghbi-rfe (_ ⨾[ _ ]⨾ si[yx])) = siʳ∈ex si[yx]
  ghbiʳ∈ex (ghbi-coe (_ ⨾[ _ ]⨾ si[yx])) = siʳ∈ex si[yx]
  ghbiʳ∈ex (ghbi-fre (_ ⨾[ _ ]⨾ si[yx])) = siʳ∈ex si[yx]
