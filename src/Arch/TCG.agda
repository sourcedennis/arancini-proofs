{-# OPTIONS --safe #-}

module Arch.TCG where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Function using (_∘_)
open import Data.Product using (_,_; _×_; proj₁; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty; _∈_)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
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

  ACQ : LabF -- acquire (does nothing - see also `Arch.TCG.Detour`)
  REL : LabF -- release (does nothing - see also `Arch.TCG.Detour`)
  SC  : LabF -- Full Fence (Sequentially Consistent)


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
lab-f-dec≡ ACQ       ACQ = yes refl
lab-f-dec≡ REL       REL = yes refl
lab-f-dec≡ SC        SC  = yes refl
lab-f-dec≡ ACQ       (_ 𝐹 _) = no (λ())
lab-f-dec≡ ACQ       REL     = no (λ())
lab-f-dec≡ ACQ       SC      = no (λ())
lab-f-dec≡ REL       (_ 𝐹 _) = no (λ())
lab-f-dec≡ REL       ACQ     = no (λ())
lab-f-dec≡ REL       SC      = no (λ())
lab-f-dec≡ SC        (_ 𝐹 _) = no (λ())
lab-f-dec≡ SC        ACQ     = no (λ())
lab-f-dec≡ SC        REL     = no (λ())
lab-f-dec≡ (_ 𝐹 _)   ACQ     = no (λ())
lab-f-dec≡ (_ 𝐹 _)   REL     = no (λ())
lab-f-dec≡ (_ 𝐹 _)   SC      = no (λ())

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


module Relations (ex : Execution {arch-TCG}) where

  open Π.Defs ex


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
    ord-init      : ( ⦗ EvInit ⦘ ⨾ po ) x y → Ord x y

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


    -- other fences

    ord-acq       : ( ⦗ EvFₜ ACQ ⦘ ⨾ po ) x y → Ord x y
    ord-rel       : ( po ⨾ ⦗ EvFₜ REL ⦘ ) x y → Ord x y

    ord-sc₁       : ( po ⨾ ⦗ EvFₜ SC ⦘ ) x y → Ord x y
    ord-sc₂       : ( ⦗ EvFₜ SC ⦘ ⨾ po ) x y → Ord x y


    -- other ordering operations

    ord-rmw-dom   : ( po ⨾ ⦗ dom rmw ⦘ )   x y → Ord x y
    ord-rmw-codom : ( ⦗ codom rmw ⦘ ⨾ po ) x y → Ord x y

    ord-w         : ( po ⨾ ⦗ EvWₜ trmw ⦘ ) x y → Ord x y
    ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ) x y → Ord x y


  -- | Immediate global happens before. (See `ghb` below)
  data Ghbi (x y : Event) : Set where
    ghbi-ord : Ord x y → Ghbi x y
    ghbi-rfe : rfe x y → Ghbi x y
    ghbi-coe : coe x y → Ghbi x y
    ghbi-fre : fre x y → Ghbi x y

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
      ax-coherence  : Acyclic _≡_ Coh
      ax-atomicity  : Empty₂ (rmw ∩₂ (fre ⨾ coe))
      ax-global-ord : Irreflexive _≡_ ghb


module Properties {ex : Execution {arch-TCG}} (wf : WellFormed ex) where

  open Relations ex
  open Π.Defs ex
  open Π.WfDefs wf

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
  ord⇒po (ord-init ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
  ord⇒po (ord-rr rr[xy]) = ord-f⇒po rr[xy]
  ord⇒po (ord-rw rw[xy]) = ord-f⇒po rw[xy]
  ord⇒po (ord-rm rm[xy]) = ord-f⇒po rm[xy]
  ord⇒po (ord-wr rw[xy]) = ord-f⇒po rw[xy]
  ord⇒po (ord-ww ww[xy]) = ord-f⇒po ww[xy]
  ord⇒po (ord-wm wm[xy]) = ord-f⇒po wm[xy]
  ord⇒po (ord-mr mr[xy]) = ord-f⇒po mr[xy]
  ord⇒po (ord-mw mw[xy]) = ord-f⇒po mw[xy]
  ord⇒po (ord-mm mm[xy]) = ord-f⇒po mm[xy]
  ord⇒po (ord-acq ((refl , _) ⨾[ _ ]⨾ po[xy]))       = po[xy]
  ord⇒po (ord-rel (po[xy] ⨾[ _ ]⨾ (refl , _)))       = po[xy]
  ord⇒po (ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , _)))       = po[xy]
  ord⇒po (ord-sc₂ ((refl , _) ⨾[ _ ]⨾ po[xy]))       = po[xy]
  ord⇒po (ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , _)))   = po[xy]
  ord⇒po (ord-rmw-codom ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
  ord⇒po (ord-w (po[xy] ⨾[ _ ]⨾ (refl , _)))         = po[xy]
  ord⇒po (ord-r ((refl , _) ⨾[ _ ]⨾ po[xy]))         = po[xy]

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

  ghbi-irreflexive : Irreflexive _≡_ Ghbi
  ghbi-irreflexive refl (ghbi-ord ord[xx]) = ord-irreflexive refl ord[xx]
  ghbi-irreflexive refl (ghbi-rfe rfe[xx]) = rf-irreflexive refl (proj₁ rfe[xx])
  ghbi-irreflexive refl (ghbi-coe coe[xx]) = co-irreflexive refl (proj₁ coe[xx])
  ghbi-irreflexive refl (ghbi-fre fre[xx]) = fr-irreflexive refl (proj₁ fre[xx])


  ordˡ∈ex : Ord ˡ∈ex
  ordˡ∈ex = poˡ∈ex ∘ ord⇒po

  ordʳ∈ex : Ord ʳ∈ex
  ordʳ∈ex = poʳ∈ex ∘ ord⇒po


  ghbiˡ∈ex : Ghbi ˡ∈ex
  ghbiˡ∈ex (ghbi-ord ord[xy]) = ordˡ∈ex ord[xy]
  ghbiˡ∈ex (ghbi-rfe rfe[xy]) = rfˡ∈ex (proj₁ rfe[xy])
  ghbiˡ∈ex (ghbi-coe coe[xy]) = coˡ∈ex (proj₁ coe[xy])
  ghbiˡ∈ex (ghbi-fre fre[xy]) = frˡ∈ex (proj₁ fre[xy])

  ghbiʳ∈ex : Ghbi ʳ∈ex
  ghbiʳ∈ex (ghbi-ord ord[xy]) = ordʳ∈ex ord[xy]
  ghbiʳ∈ex (ghbi-rfe rfe[xy]) = rfʳ∈ex (proj₁ rfe[xy])
  ghbiʳ∈ex (ghbi-coe coe[xy]) = coʳ∈ex (proj₁ coe[xy])
  ghbiʳ∈ex (ghbi-fre fre[xy]) = frʳ∈ex (proj₁ fre[xy])
