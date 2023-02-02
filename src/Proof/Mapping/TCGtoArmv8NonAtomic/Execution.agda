{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic.Execution
  {dst : Execution {arch-Armv8}}
  (dst-a8 : Armv8Execution)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst dst-a8)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Function using (_∘_)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
-- Local imports
open import Helpers
open import MapTCGtoArmv8NonAtomic
open import Arch.Armv8 as Armv8
open import Arch.TCG as TCG

open Δ.Defs


dst-consistent = Armv8-TCGRestricted.consistent dst-ok

open Armv8-TCGRestricted dst-ok


-- # Backward Mapping of Relations

-- The mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
-- Rₗ         ↦  F_FULL;Rₗ;F_FULL          || failed RMW
--
-- F_RR       ↦  F_LD
-- F_RW       ↦  F_LD
-- F_RM       ↦  F_LD
--
-- F_WW       ↦  F_ST
--
-- F_WR       ↦  F_FULL
-- F_WM       ↦  F_FULL
-- F_MR       ↦  F_FULL
-- F_MW       ↦  F_FULL
-- F_MM       ↦  F_FULL
-- F_SC       ↦  F_FULL


ev[⇐] : {x : EventArmv8} → (x∈dst : x ∈ events dst) → EventTCG
ev[⇐] {event-init uid loc val} x∈dst = event-init uid loc val
ev[⇐] x@{event-skip uid tid}   x∈dst = lemma (⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip))
  where
  lemma-f : (org-skip-acq ∪₁ org-skip-rel) x → TCG.LabF
  lemma-f (opt₁ _) = ACQ
  lemma-f (opf₂ _) = REL

  lemma : (org-skip-skip ∪₁ org-skip-acq ∪₁ org-skip-rel) x → EventTCG
  lemma (inj₁ _) = event-skip uid tid
  lemma (inj₂ o) = event-f uid tid (lemma-f o)
ev[⇐] {event-r uid tid loc val (lab-r tag)} x∈dst = event-r uid tid loc val (lab-r tag)
ev[⇐] {event-w uid tid loc val (lab-w tag)} x∈dst = event-w uid tid loc val (lab-w tag)
ev[⇐] x@{event-f uid tid (lab-f F-full)}    x∈dst = lemma (⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f))
  where
  lemma : (org-f-wr ∪₁ org-f-wm ∪₁ org-f-mr ∪₁ org-f-mw ∪₁ org-f-mm ∪₁ org-f-sc ∪₁ org-f-pre-rmw ∪₁ org-f-post-rmw) x
    → EventTCG
  lemma (opt₁ _) = event-f uid tid WR
  lemma (opt₂ _) = event-f uid tid WM
  lemma (opt₃ _) = event-f uid tid MR
  lemma (opt₄ _) = event-f uid tid MW
  lemma (opt₅ _) = event-f uid tid MM
  lemma (opt₆ _) = event-f uid tid SC
  lemma (opf₇ _) = event-skip uid tid
ev[⇐] x@{event-f uid tid (lab-f F-ld)} x∈dst = event-f uid tid (lemma (⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)))
  where
  -- This saves a pattern match in the uid/tid translations
  lemma : (org-ld-rr ∪₁ org-ld-rw ∪₁ org-ld-rm) x → TCG.LabF
  lemma (opt₁ _) = RR
  lemma (opt₂ _) = RW
  lemma (opf₃ _) = RM
ev[⇐] {event-f uid tid (lab-f F-st)} x∈dst = event-f uid tid WW
-- absent events
ev[⇐] {event-r _ _ _ _ (lab-a _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-r _ _ _ _ lab-q}     x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-w _ _ _ _ (lab-l _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-f _ _ lab-isb}       x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


-- # Proof framework

open Δ.Primitives dst-wf ev[⇐]

private
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    tag : Tag

uid[⇐] : Pred[⇐]² (HasUid uid)
uid[⇐] {_} x∈dst has-uid-init = has-uid-init
uid[⇐] {_} x∈dst has-uid-skip with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
uid[⇐] {_} x∈dst has-uid-skip | opt₁ _ = has-uid-skip
uid[⇐] {_} x∈dst has-uid-skip | opt₂ _ = has-uid-f
uid[⇐] {_} x∈dst has-uid-skip | opf₃ _ = has-uid-f
uid[⇐] {_} {event-r _ _ _ _ (lab-r _)}  x∈dst has-uid-r = has-uid-r
uid[⇐] {_} {event-w _ _ _ _ (lab-w _)}  x∈dst has-uid-w = has-uid-w
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | inj₁ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₂ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₃ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₄ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₅ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₆ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opt₇ _ = has-uid-skip
uid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f | opf₈ _ = has-uid-skip
uid[⇐] {_} {event-f _ _ (lab-f F-ld)}   x∈dst has-uid-f = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-st)}   x∈dst has-uid-f = has-uid-f
-- impossible cases
uid[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst has-uid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst has-uid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst has-uid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-f _ _ lab-isb}       x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}           x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
uid[$⇒] {_} {event-skip _ _}             x∈dst has-uid-skip | opt₁ _ = has-uid-skip
uid[$⇒] {_} {event-skip _ _}             x∈dst has-uid-f    | opf₂ _ = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ (lab-r _)}  x∈dst has-uid-r = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ (lab-w _)}  x∈dst has-uid-w = has-uid-w
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₁ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₂ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₃ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₄ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₅ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-f    | opt₆ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-skip | opt₇ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-uid-skip | opf₈ _ = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst has-uid-f = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-st)}   x∈dst has-uid-f = has-uid-f
-- impossible cases
uid[$⇒] {_} {event-r _ _ _ _ (lab-a _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-r _ _ _ _ lab-q}     x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-w _ _ _ _ (lab-l _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-f _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_} x∈dst has-tid-skip with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
tid[⇐] {_} x∈dst has-tid-skip | opt₁ _ = has-tid-skip
tid[⇐] {_} x∈dst has-tid-skip | opt₂ _ = has-tid-f
tid[⇐] {_} x∈dst has-tid-skip | opf₃ _ = has-tid-f
tid[⇐] {_} {event-r _ _ _ _ (lab-r _)}  x∈dst has-tid-r = has-tid-r
tid[⇐] {_} {event-w _ _ _ _ (lab-w _)}  x∈dst has-tid-w = has-tid-w
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | inj₁ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₂ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₃ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₄ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₅ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₆ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opt₇ _ = has-tid-skip
tid[⇐] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f | opf₈ _ = has-tid-skip
tid[⇐] {_} {event-f _ _ (lab-f F-ld)}   x∈dst has-tid-f = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-st)}   x∈dst has-tid-f = has-tid-f
-- impossible cases
tid[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst has-tid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst has-tid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst has-tid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-f _ _ lab-isb}       x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
tid[$⇒] {_} {event-skip _ _}             x∈dst has-tid-skip | opt₁ _ = has-tid-skip
tid[$⇒] {_} {event-skip _ _}             x∈dst has-tid-f    | opf₂ _ = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ (lab-r _)}  x∈dst has-tid-r = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ (lab-w _)}  x∈dst has-tid-w = has-tid-w
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₁ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₂ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₃ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₄ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₅ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-f    | opt₆ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-skip | opt₇ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst has-tid-skip | opf₈ _ = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst has-tid-f = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-st)}   x∈dst has-tid-f = has-tid-f
-- impossible cases
tid[$⇒] {_} {event-r _ _ _ _ (lab-a _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-r _ _ _ _ lab-q}     x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-w _ _ _ _ (lab-l _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-f _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init = has-loc-init
loc[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst has-loc-r = has-loc-r
loc[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst has-loc-w = has-loc-w
-- impossible cases
loc[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst has-loc-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst has-loc-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst has-loc-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}        x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ (lab-r _)} x∈dst has-loc-r  = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst has-loc-w  = has-loc-w
-- impossible cases
loc[$⇒] {_} {event-skip _ _}           x∈dst x-loc with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
loc[$⇒] {_} {event-skip _ _} x∈dst x-loc | opt₁ _ = ⊥-elim (¬skip-loc ev-skip (_ , x-loc))
loc[$⇒] {_} {event-skip _ _} x∈dst x-loc | opf₂ _ = ⊥-elim (¬f-loc ev-f (_ , x-loc))
loc[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _     with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
loc[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst x-loc | opf₇ _ = ⊥-elim (¬skip-loc ev-skip (_ , x-loc))
loc[$⇒] {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-r _ _ _ _ lab-q}      x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-w _ _ _ _ (lab-l _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst x-loc = ⊥-elim (¬f-loc ev-f (_ , x-loc))
loc[$⇒] {_} {event-f _ _ (lab-f F-st)}   x∈dst x-loc = ⊥-elim (¬f-loc ev-f (_ , x-loc))


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init = has-val-init
val[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst has-val-r = has-val-r
val[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst has-val-w = has-val-w
-- impossible cases
val[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst has-val-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst has-val-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst has-val-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}        x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ (lab-r _)} x∈dst has-val-r  = has-val-r
val[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst has-val-w  = has-val-w
-- impossible cases
val[$⇒] {_} {event-skip _ _}           x∈dst x-val with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
val[$⇒] {_} {event-skip _ _} x∈dst x-val | opt₁ _ = ⊥-elim (¬skip-val ev-skip (_ , x-val))
val[$⇒] {_} {event-skip _ _} x∈dst x-val | opf₂ _ = ⊥-elim (¬f-val ev-f (_ , x-val))
val[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _     with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
val[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst x-val | opf₇ _ = ⊥-elim (¬skip-val ev-skip (_ , x-val))
val[$⇒] {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-r _ _ _ _ lab-q}      x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-w _ _ _ _ (lab-l _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst x-val = ⊥-elim (¬f-val ev-f (_ , x-val))
val[$⇒] {_} {event-f _ _ (lab-f F-st)}   x∈dst x-val = ⊥-elim (¬f-val ev-f (_ , x-val))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}         x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
Init[$⇒] {event-skip _ _}             x∈dst () | opt₁ _
Init[$⇒] {event-skip _ _}             x∈dst () | opf₂ _
Init[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
Init[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
Init[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-r _ _  _ _ lab-q}     x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-w _ _  _ _ (lab-l _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐]                                 x∈dst (ev-init refl) = ev-init refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst (ev-w refl)    = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}          x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
Wₜ[$⇒] {_} {event-skip _ _}             x∈dst () | opt₁ _
Wₜ[$⇒] {_} {event-skip _ _}             x∈dst () | opf₂ _
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst ()
Wₜ[$⇒] {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst (ev-r refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst (ev-r refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[$⇒] : Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r _)}  x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
Rₜ[$⇒] {_} {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst () | opt₁ _
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst () | opf₂ _
Rₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _)}  x∈dst ()
Rₜ[$⇒] {_} {event-f _ _ (lab-f F-ld)}   x∈dst ()
Rₜ[$⇒] {_} {event-f _ _ (lab-f F-st)}   x∈dst ()
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-w _ _ _ _ (lab-l _ )} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


ψ : GeneralFramework
ψ =
  record
    { ev[⇐]    = ev[⇐]
    ; uid[⇐]   = uid[⇐]
    ; uid[$⇒]  = uid[$⇒]
    ; tid[⇐]   = tid[⇐]
    ; tid[$⇒]  = tid[$⇒]
    ; Init[⇐]  = Init[⇐]
    ; Init[$⇒] = Init[$⇒]
    }

δ : MappingFramework
δ =
  record
    { ψ       = ψ
    ; loc[⇐]  = loc[⇐]
    ; loc[$⇒] = loc[$⇒]
    ; val[⇐]  = val[⇐]
    ; val[$⇒] = val[$⇒]
    ; Wₜ[⇐]   = Wₜ[⇐]
    ; Wₜ[$⇒]  = Wₜ[$⇒]
    ; Rₜ[⇐]   = Rₜ[⇐]
    ; Rₜ[$⇒]  = Rₜ[$⇒]
    }


-- # Extra helpers

module Extra where

  open import Burrow.Framework.Mapping.Definitions δ
  open import Burrow.Framework.WellFormed ψ using (rmw[⇒])
  open Armv8Execution


  rmw[⇒]lxsx : Rel[⇒] (rmw src) (lxsx dst-a8)
  rmw[⇒]lxsx x∈src y∈src = rmw⇒lxsx dst-ok dst-wf ∘ rmw[⇒] x∈src y∈src


  R₌[$⇒] : Pred[$⇒] (EvR₌ loc val (lab-r tag)) (EvR₌ loc val (lab-r tag))
  R₌[$⇒] {_} {_} {_} {event-r _ _ _ _ (lab-r _)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  R₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst () | opt₁ _
  R₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst () | opf₂ _
  R₌[$⇒] {_} {_} {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  R₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | opt₇ _
  R₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | opf₈ _
  
  R₌[⇒] : Pred[⇒] (EvR₌ loc val (lab-r tag)) (EvR₌ loc val (lab-r tag))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (lab-w tag)) (EvW₌ loc val (lab-w tag))
  W₌[$⇒] {_} {_} {_} {event-w _ _ _ _ (lab-w _)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  W₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst () | opt₁ _
  W₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst () | opf₂ _
  W₌[$⇒] {_} {_} {_} {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  W₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | opt₇ _
  W₌[$⇒] {_} {_} {_} {event-f _ _ (lab-f F-full)} x∈dst () | opf₈ _
  
  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tag)) (EvW₌ loc val (lab-w tag))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  -- Map fences. RR / RW / RM / WR / WW / WM / MR / MW / MM / SC
  --
  -- RR / RW / RM                -> F-ld
  -- WW                          -> F-st
  -- WR / WM / MR / MW / MM / SC -> F-full

  Frr[$⇒] : Pred[$⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ = ev-f
  -- impossible cases
  Frr[$⇒] {event-init _ _ _}           x∈dst ()
  Frr[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Frr[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Frr[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
    
  Frr[⇒] : Pred[⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[⇒] = [$⇒]→₁[⇒] Frr[$⇒]


  Frw[$⇒] : Pred[$⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ = ev-f
  -- impossible cases
  Frw[$⇒] {event-init _ _ _}           x∈dst ()
  Frw[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Frw[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Frw[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
    
  Frw[⇒] : Pred[⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[⇒] = [$⇒]→₁[⇒] Frw[$⇒]
  
  
  Frm[$⇒] : Pred[$⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ = ev-f
  -- impossible cases
  Frm[$⇒] {event-init _ _ _}           x∈dst ()
  Frm[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Frm[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Frm[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
    
  Frm[⇒] : Pred[⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[⇒] = [$⇒]→₁[⇒] Frm[$⇒]


  Fww[$⇒] : Pred[$⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[$⇒] {event-f _ _ (lab-f F-st)}   x∈dst ev-f = ev-f
  -- impossible cases
  Fww[$⇒] {event-init _ _ _}           x∈dst ()
  Fww[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-w _ _  _ _ (lab-l _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fww[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fww[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _

  Fww[⇒] : Pred[⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[⇒] = [$⇒]→₁[⇒] Fww[$⇒]
  

  Fwr[$⇒] : Pred[$⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fwr[$⇒] {event-init _ _ _}           x∈dst ()
  Fwr[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fwr[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fwr[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fwr[⇒] : Pred[⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[⇒] = [$⇒]→₁[⇒] Fwr[$⇒]


  Fwm[$⇒] : Pred[$⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fwm[$⇒] {event-init _ _ _}           x∈dst ()
  Fwm[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fwm[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fwm[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fwm[⇒] : Pred[⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[⇒] = [$⇒]→₁[⇒] Fwm[$⇒]


  Fmr[$⇒] : Pred[$⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmr[$⇒] {event-init _ _ _}           x∈dst ()
  Fmr[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fmr[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fmr[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fmr[⇒] : Pred[⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[⇒] = [$⇒]→₁[⇒] Fmr[$⇒]


  Fmw[$⇒] : Pred[$⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmw[$⇒] {event-init _ _ _}           x∈dst ()
  Fmw[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fmw[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fmw[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fmw[⇒] : Pred[⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[⇒] = [$⇒]→₁[⇒] Fmw[$⇒]
  

  Fmm[$⇒] : Pred[$⇒] (EvFₜ MM) (EvFₘ F-full)
  Fmm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmm[$⇒] {event-init _ _ _}           x∈dst ()
  Fmm[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fmm[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fmm[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fmm[⇒] : Pred[⇒] (EvFₜ MM) (EvFₘ F-full)
  Fmm[⇒] = [$⇒]→₁[⇒] Fmm[$⇒]


  Fsc[$⇒] : Pred[$⇒] (EvFₜ SC) (EvFₘ F-full)
  Fsc[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fsc[$⇒] {event-init _ _ _}           x∈dst ()
  Fsc[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Fsc[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fsc[$⇒] {event-skip _ _}             x∈dst () | opf₃ _
  Fsc[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fsc[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fsc[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fsc[⇒] : Pred[⇒] (EvFₜ SC) (EvFₘ F-full)
  Fsc[⇒] = [$⇒]→₁[⇒] Fsc[$⇒]


  Facq[$⇒] : Pred[$⇒] (EvFₜ ACQ) EvSkip
  Facq[$⇒] {event-skip _ _} x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Facq[$⇒] {event-skip _ _} x∈dst _ | opt₂ _ = ev-skip
  -- impossible cases
  Facq[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Facq[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Facq[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
  Facq[$⇒] {event-init _ _ _}           x∈dst ()
  Facq[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Facq[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Facq[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Facq[⇒] : Pred[⇒] (EvFₜ ACQ) EvSkip
  Facq[⇒] = [$⇒]→₁[⇒] Facq[$⇒]
  

  Frel[$⇒] : Pred[$⇒] (EvFₜ REL) EvSkip
  Frel[$⇒] {event-skip _ _} x∈dst _ with ⇔₁-apply-⊆₁ org-skip-def (x∈dst , ev-skip)
  Frel[$⇒] {event-skip _ _} x∈dst _ | opf₃ _ = ev-skip
  -- impossible cases
  Frel[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frel[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₆ _
  Frel[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₇ _
  Frel[$⇒] {event-init _ _ _}           x∈dst ()
  Frel[$⇒] {event-r _ _ _ _ (lab-a _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event-r _ _ _ _ lab-q}      x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event-w _ _ _ _ (lab-l _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Frel[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Frel[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Frel[⇒] : Pred[⇒] (EvFₜ REL) EvSkip
  Frel[⇒] = [$⇒]→₁[⇒] Frel[$⇒]
  

  F[⇒]ld : {m : TCG.LabF} → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
    → Pred[⇒] (EvFₜ m) (EvFₘ F-ld)
  F[⇒]ld (here refl)                 = Frr[⇒]
  F[⇒]ld (there (here refl))         = Frw[⇒]
  F[⇒]ld (there (there (here refl))) = Frm[⇒]
  
  F[⇒]ff : {m : TCG.LabF} → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
    → Pred[⇒] (EvFₜ m) (EvFₘ F-full)
  F[⇒]ff (here refl)                                         = Fwr[⇒]
  F[⇒]ff (there (here refl))                                 = Fwm[⇒]
  F[⇒]ff (there (there (here refl)))                         = Fmr[⇒]
  F[⇒]ff (there (there (there (here refl))))                 = Fmw[⇒]
  F[⇒]ff (there (there (there (there (here refl)))))         = Fmm[⇒]
  F[⇒]ff (there (there (there (there (there (here refl)))))) = Fsc[⇒]
  
  F[⇒]skip : {m : TCG.LabF} → m ∈ₗ (ACQ ∷ REL ∷ [])
    → Pred[⇒] (EvFₜ m) EvSkip
  F[⇒]skip (here refl)         = Facq[⇒]
  F[⇒]skip (there (here refl)) = Frel[⇒]
