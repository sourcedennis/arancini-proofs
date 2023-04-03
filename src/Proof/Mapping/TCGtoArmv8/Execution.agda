{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8 using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8.Execution
  {dst : Execution {arch-Armv8}}
  {dst-a8 : Armv8Execution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst-a8)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Function using (_∘_; flip)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary hiding (REL)
-- Local imports
open import Helpers
open import MapTCGtoArmv8
open import Arch.Armv8 as Armv8
open import Arch.TCG as TCG

open Δ.Defs


dst-consistent = Armv8-TCGRestricted.consistent dst-ok

open Armv8-TCGRestricted dst-ok


-- # Backward Mapping of Relations


-- The (forward) mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  Aₗ;amo;Lₗ  || successful RMW
-- Rₗ         ↦  Lₗ         || failed RMW
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


ev[⇐] : {x : EventArmv8} → (x∈dst : x ∈ events dst) → EventTCG
ev[⇐] {event-init uid loc val} x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}     x∈dst = event-skip uid tid
ev[⇐] {event-r uid tid loc val (lab-r tmov)} x∈dst = event-r uid tid loc val (lab-r tmov)
ev[⇐] {event-w uid tid loc val (lab-w tmov)} x∈dst = event-w uid tid loc val (lab-w tmov)
ev[⇐] {event-r uid tid loc val (lab-a trmw)} x∈dst = event-r uid tid loc val (lab-r trmw)
ev[⇐] {event-w uid tid loc val (lab-l trmw)} x∈dst = event-w uid tid loc val (lab-w trmw)
ev[⇐] x@{event-f uid tid (lab-f F-full)}     x∈dst =
  event-f uid tid (lemma (⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)))
  where
  -- This saves a pattern match in the uid/tid translations
  lemma : (org-f-wr ∪₁ org-f-wm ∪₁ org-f-mr ∪₁ org-f-mw ∪₁ org-f-mm) x → TCG.LabF
  lemma (opt₁ _) = WR
  lemma (opt₂ _) = WM
  lemma (opt₃ _) = MR
  lemma (opt₄ _) = MW
  lemma (opf₅ _) = MM
ev[⇐] x@{event-f uid tid (lab-f F-ld)}      x∈dst = event-f uid tid (lemma (⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)))
  where
  -- This saves a pattern match in the uid/tid translations
  lemma : (org-ld-rr ∪₁ org-ld-rw ∪₁ org-ld-rm) x → TCG.LabF
  lemma (opt₁ _) = RR
  lemma (opt₂ _) = RW
  lemma (opf₃ _) = RM
ev[⇐] {event-f uid tid (lab-f F-st)}      x∈dst = event-f uid tid WW
-- absent events
ev[⇐] {event-r _ _ _ _ lab-q}        x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-f _ _ lab-isb}          x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-r _ _ _ _ (lab-r trmw)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-w _ _ _ _ (lab-w trmw)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-r _ _ _ _ (lab-a tmov)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event-w _ _ _ _ (lab-l tmov)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


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
uid[⇐] {_} x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-uid-r = has-uid-r
uid[⇐] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-uid-r = has-uid-r
uid[⇐] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-uid-w = has-uid-w
uid[⇐] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-uid-w = has-uid-w
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f | opt₁ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f | opt₂ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f | opt₃ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f | opt₄ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f | opf₅ _ = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-ld)}     x∈dst has-uid-f = has-uid-f
uid[⇐] {_} {event-f _ _ (lab-f F-st)}     x∈dst has-uid-f = has-uid-f
-- impossible cases
uid[⇐] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst has-uid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst has-uid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst has-uid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-r _ _ _ _ lab-q}        x∈dst has-uid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst has-uid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event-f _ _ lab-isb}          x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst λ())

uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}             x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}               x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-uid-r = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-uid-w = has-uid-w
uid[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-uid-r = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-uid-w = has-uid-w
uid[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-uid-f = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-ld)}     x∈dst has-uid-f = has-uid-f
uid[$⇒] {_} {event-f _ _ (lab-f F-st)}     x∈dst has-uid-f = has-uid-f
-- impossible cases
uid[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())

    
tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_} x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-tid-r = has-tid-r
tid[⇐] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-tid-r = has-tid-r
tid[⇐] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-tid-w = has-tid-w
tid[⇐] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-tid-w = has-tid-w
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f | inj₁ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f | opt₂ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f | opt₃ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f | opt₄ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f | opf₅ _ = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-ld)}     x∈dst has-tid-f = has-tid-f
tid[⇐] {_} {event-f _ _ (lab-f F-st)}     x∈dst has-tid-f = has-tid-f
-- impossible cases
tid[⇐] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst has-tid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst has-tid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst has-tid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-r _ _ _ _ lab-q}        x∈dst has-tid-r = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst has-tid-w = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event-f _ _ lab-isb}          x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst λ())

tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}               x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst has-tid-f    = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-ld)}     x∈dst has-tid-f    = has-tid-f
tid[$⇒] {_} {event-f _ _ (lab-f F-st)}     x∈dst has-tid-f    = has-tid-f
-- impossible cases
tid[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] {_}                                x∈dst has-loc-init = has-loc-init
loc[⇐] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-loc-r = has-loc-r
loc[⇐] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-loc-w = has-loc-w
loc[⇐] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-loc-r = has-loc-r
loc[⇐] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-loc-w = has-loc-w
-- impossible cases
loc[⇐] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst has-loc-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst has-loc-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst has-loc-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst has-loc-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] {_} {event-r _ _ _ _ lab-q}        x∈dst has-loc-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}             x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-loc-w    = has-loc-w
loc[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-loc-w    = has-loc-w
-- impossible cases
loc[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst x-loc = ⊥-elim (¬f-loc ev-f (_ , x-loc))
loc[$⇒] {_} {event-f _ _ (lab-f F-ld)}     x∈dst x-loc = ⊥-elim (¬f-loc ev-f (_ , x-loc))
loc[$⇒] {_} {event-f _ _ (lab-f F-st)}     x∈dst x-loc = ⊥-elim (¬f-loc ev-f (_ , x-loc))


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] {_}                                x∈dst has-val-init = has-val-init
val[⇐] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-val-r = has-val-r
val[⇐] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-val-w = has-val-w
val[⇐] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-val-r = has-val-r
val[⇐] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-val-w = has-val-w
-- impossible cases
val[⇐] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst has-val-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst has-val-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst has-val-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst has-val-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] {_} {event-r _ _ _ _ lab-q}        x∈dst has-val-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}             x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst has-val-w    = has-val-w
val[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst has-val-w    = has-val-w
-- impossible cases
val[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst x-val = ⊥-elim (¬f-val ev-f (_ , x-val))
val[$⇒] {_} {event-f _ _ (lab-f F-ld)}     x∈dst x-val = ⊥-elim (¬f-val ev-f (_ , x-val))
val[$⇒] {_} {event-f _ _ (lab-f F-st)}     x∈dst x-val = ⊥-elim (¬f-val ev-f (_ , x-val))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}           x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-f _ _ (lab-f F-full)}     x∈dst ()
Init[$⇒] {event-r _ _ _ _ (lab-r trmw)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-w _ _ _ _ (lab-w trmw)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-r _ _ _ _ (lab-a tmov)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-w _ _ _ _ (lab-l tmov)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-r _ _ _ _ lab-q}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ lab-isb}            x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] {_}                                x∈dst (ev-init refl) = ev-init refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst (ev-w refl)    = ev-w refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst (ev-w refl)    = ev-w refl
-- impossible cases
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst (ev-w refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst (ev-w refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}             x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst (ev-w refl)    = ev-w refl
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst (ev-w refl)    = ev-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst ()
Wₜ[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst ()
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-ld)}     x∈dst ()
Wₜ[$⇒] {_} {event-f _ _ (lab-f F-st)}     x∈dst ()
Wₜ[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst (ev-r refl) = ev-r refl
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst (ev-r refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst (ev-r refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[⇐] {_} {event-r _ _ _ _ lab-q}        x∈dst (ev-r refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst (ev-r refl) = ev-r refl
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


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
  open import Burrow.Framework.WellFormed ψ using (rmw[⇒]; rel[$⇒]; rel[⇐])
  open Armv8Execution
  open Δ.Consistency δ using (rmwˡ-r; rmwʳ-w; ev[⇐$]eq)

  open Arch.Armv8.Properties dst-a8 dst-wf


  -- # Map the Armv8Execution to a TCGExecution

  src-si : Rel₀ EventTCG
  src-si = src-rel siˡ∈ex siʳ∈ex

  si[$⇒] : Rel[$⇒] src-si (si dst-a8)
  si[$⇒] = rel[$⇒] siˡ∈ex siʳ∈ex

  si[⇒] : Rel[⇒] src-si (si dst-a8)
  si[⇒] = [$⇒]→₂[⇒] si[$⇒]

  si[⇐] : Rel[⇐] src-si (si dst-a8)
  si[⇐] = rel[⇐] siˡ∈ex siʳ∈ex
  
  si[⇐$] : Rel[⇐$] src-si (si dst-a8)
  si[⇐$] = [⇐]→₂[⇐$] si[⇐]

  siˡ∈src : {x y : EventTCG} → src-si x y → x ∈ events src
  siˡ∈src = relˡ∈src siˡ∈ex siʳ∈ex
  
  siʳ∈src : {x y : EventTCG} → src-si x y → y ∈ events src
  siʳ∈src = relʳ∈src siˡ∈ex siʳ∈ex

  src-si-internal : src-si ⊆₂ po src ∪₂ flip (po src) ∪₂ ⦗ events src ⦘
  src-si-internal = ⊆: λ{x y si[xy]ˢ →
      let x∈src = siˡ∈src si[xy]ˢ
          y∈src = siʳ∈src si[xy]ˢ
          si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
      in
      case ⊆₂-apply (si-internal dst-a8) si[xy]ᵗ of
      λ{ (opt₁ po[xy]ᵗ) → opt₁ (po[⇐$] x∈src y∈src po[xy]ᵗ)
       ; (opt₂ po[yx]ᵗ) → opt₂ (po[⇐$] y∈src x∈src po[yx]ᵗ)
       ; (opf₃ (x≡y , _)) → opf₃ (ev[⇐$]eq x∈src y∈src x≡y , x∈src)
       }
    }

  src-si-refl : Reflexive (filter-rel (events src) src-si)
  src-si-refl {with-pred xˢ x∈src} =
    let xᵗ = ev[⇒] x∈src
        x∈dst = events[⇒] x∈src
        si[xx]ᵗ = si-refl dst-a8 {with-pred xᵗ x∈dst}
    in si[⇐$] x∈src x∈src si[xx]ᵗ

  src-si-sym : Symmetric src-si
  src-si-sym {xˢ} {yˢ} si[xy]ˢ =
    let x∈src = siˡ∈src si[xy]ˢ
        y∈src = siʳ∈src si[xy]ˢ
        si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
        si[yx]ᵗ = si-sym dst-a8 si[xy]ᵗ
    in si[⇐$] y∈src x∈src si[yx]ᵗ

  src-si-trans : Transitive src-si
  src-si-trans {xˢ} {yˢ} {zˢ} si[xy]ˢ si[yz]ˢ =
    let x∈src = siˡ∈src si[xy]ˢ
        y∈src = siʳ∈src si[xy]ˢ
        z∈src = siʳ∈src si[yz]ˢ
        si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
        si[yz]ᵗ = si[⇒] y∈src z∈src si[yz]ˢ
        si[xz]ᵗ = si-trans dst-a8 si[xy]ᵗ si[yz]ᵗ
    in si[⇐$] x∈src z∈src si[xz]ᵗ

  src-tex : TCGExecution src
  src-tex =
    record {
      si          = src-si
    ; si-internal = src-si-internal
    ; si-refl     = λ {x} → src-si-refl {x}
    ; si-sym      = src-si-sym
    ; si-trans    = src-si-trans
    }


  Rₜ[⇒]A : Pred[⇒] (EvRₜ trmw) EvA
  Rₜ[⇒]A x∈src = Rₐ⇒A dst-ok (events[⇒] x∈src) ∘ Rₜ[⇒] x∈src

  Wₜ[⇒]L : Pred[⇒] (EvWₜ trmw) EvL
  Wₜ[⇒]L x∈src = Wₐ⇒L dst-ok (events[⇒] x∈src) ∘ Wₜ[⇒] x∈src

  rmw[⇒]amo : Rel[⇒] (rmw src) (amo dst-a8)
  rmw[⇒]amo x∈src y∈src = rmw⇒amo dst-ok dst-wf ∘ (rmw[⇒] x∈src y∈src)
  
  rmw[⇒]amo-al : Rel[⇒] (rmw src) (⦗ EvA ⦘ ⨾ amo dst-a8 ⨾ ⦗ EvL ⦘)
  rmw[⇒]amo-al x∈src y∈src rmw[xy] =
    let dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        x-a = Rₐ⇒A dst-ok (events[⇒] x∈src) (rmwˡ-r dst-wf (take-dom (rmw dst) dst-rmw[xy]))
        y-l = Wₐ⇒L dst-ok (events[⇒] y∈src) (rmwʳ-w dst-wf (take-codom (rmw dst) dst-rmw[xy]))
    in (refl , x-a) ⨾[ _ ]⨾ rmw[⇒]amo x∈src y∈src rmw[xy] ⨾[ _ ]⨾ (refl , y-l)
  
  R₌[$⇒] : Pred[$⇒] (EvR₌ loc val (lab-r tmov)) (EvR₌ loc val (lab-r tmov))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r tmov)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
  R₌[$⇒] {_} {_} {event-f _ _ (lab-f F-ld)}     x∈dst ()
  R₌[$⇒] {_} {_} {event-f _ _ (lab-f F-st)}     x∈dst ()
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-skip _ _}               x∈dst ()
  
  R₌[⇒] : Pred[⇒] (EvR₌ loc val (lab-r tmov)) (EvR₌ loc val (lab-r tmov))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  R₌[$⇒]A : Pred[$⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-a trmw))
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ (lab-a trmw)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒]A {_} {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
  R₌[$⇒]A {_} {_} {event-f _ _ (lab-f F-ld)}     x∈dst ()
  R₌[$⇒]A {_} {_} {event-f _ _ (lab-f F-st)}     x∈dst ()
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]A {_} {_} {event-skip _ _}               x∈dst ()
  
  R₌[⇒]A : Pred[⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-a trmw))
  R₌[⇒]A = [$⇒]→₁[⇒] R₌[$⇒]A
    

  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
  W₌[$⇒] {_} {_} {event-f _ _ (lab-f F-ld)}     x∈dst ()
  W₌[$⇒] {_} {_} {event-f _ _ (lab-f F-st)}     x∈dst ()
  W₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-skip _ _}               x∈dst ()
  
  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  W₌[$⇒]L : Pred[$⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-l trmw))
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-l trmw)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-w tmov)} x∈dst ()
  W₌[$⇒]L {_} {_} {event-f _ _ (lab-f F-full)}   x∈dst ()
  W₌[$⇒]L {_} {_} {event-f _ _ (lab-f F-ld)}     x∈dst ()
  W₌[$⇒]L {_} {_} {event-f _ _ (lab-f F-st)}     x∈dst ()
  W₌[$⇒]L {_} {_} {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]L {_} {_} {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]L {_} {_} {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]L {_} {_} {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  W₌[⇒]L : Pred[⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-l trmw))
  W₌[⇒]L = [$⇒]→₁[⇒] W₌[$⇒]L


  -- Map fences. RR / RW / RM / WR / WW / WM / MR / MW / MM / SC
  --
  -- RR / RW / RM                → F-ld
  -- WW                          → F-st
  -- WR / WM / MR / MW / MM / SC → F-full

  Frr[$⇒] : Pred[$⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ = ev-f
  -- impossible cases
  Frr[$⇒] {event-init _ _ _}             x∈dst ()
  Frr[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-skip _ _}               x∈dst ()
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₁ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₂ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₃ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₄ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opf₅ _
    
  Frr[⇒] : Pred[⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[⇒] = [$⇒]→₁[⇒] Frr[$⇒]


  Frw[$⇒] : Pred[$⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ = ev-f
  -- impossible cases
  Frw[$⇒] {event-init _ _ _}             x∈dst ()
  Frw[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-skip _ _}               x∈dst ()
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₁ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₂ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₃ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₄ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opf₅ _
    
  Frw[⇒] : Pred[⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[⇒] = [$⇒]→₁[⇒] Frw[$⇒]


  Frm[$⇒] : Pred[$⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ = ev-f
  -- impossible cases
  Frm[$⇒] {event-init _ _ _}             x∈dst ()
  Frm[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-skip _ _}               x∈dst ()
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₁ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₂ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₃ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opt₄ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opf₅ _
    
  Frm[⇒] : Pred[⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[⇒] = [$⇒]→₁[⇒] Frm[$⇒]


  Fww[$⇒] : Pred[$⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[$⇒] {event-f _ _ (lab-f F-st)}   x∈dst _ = ev-f
  -- impossible cases
  Fww[$⇒] {event-init _ _ _}             x∈dst ()
  Fww[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-skip _ _}               x∈dst ()
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
  Fww[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst () | opf₅ _
  
  Fww[⇒] : Pred[⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[⇒] = [$⇒]→₁[⇒] Fww[$⇒]
  

  Fwr[$⇒] : Pred[$⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ = ev-f
  -- impossible cases
  Fwr[$⇒] {event-init _ _ _}             x∈dst ()
  Fwr[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-skip _ _}               x∈dst ()
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
    
  Fwr[⇒] : Pred[⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[⇒] = [$⇒]→₁[⇒] Fwr[$⇒]


  Fwm[$⇒] : Pred[$⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ = ev-f
  -- impossible cases
  Fwm[$⇒] {event-init _ _ _}             x∈dst ()
  Fwm[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-skip _ _}               x∈dst ()
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
    
  Fwm[⇒] : Pred[⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[⇒] = [$⇒]→₁[⇒] Fwm[$⇒]


  Fmr[$⇒] : Pred[$⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ = ev-f
  -- impossible cases
  Fmr[$⇒] {event-init _ _ _}             x∈dst ()
  Fmr[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-skip _ _}               x∈dst ()
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
    
  Fmr[⇒] : Pred[⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[⇒] = [$⇒]→₁[⇒] Fmr[$⇒]


  Fmw[$⇒] : Pred[$⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ = ev-f
  -- impossible cases
  Fmw[$⇒] {event-init _ _ _}             x∈dst ()
  Fmw[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-skip _ _}               x∈dst ()
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
    
  Fmw[⇒] : Pred[⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[⇒] = [$⇒]→₁[⇒] Fmw[$⇒]


  Fmm[$⇒] : Pred[$⇒] (EvFₜ MM) (EvFₘ F-full)
  Fmm[$⇒] {event-f _ _ (lab-f F-full)}   x∈dst _ = ev-f
  -- impossible cases
  Fmm[$⇒] {event-init _ _ _}             x∈dst ()
  Fmm[$⇒] {event-r _ _ _ _ (lab-r trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-w _ _ _ _ (lab-w trmw)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-r _ _ _ _ (lab-a tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-w _ _ _ _ (lab-l tmov)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-r _ _ _ _ lab-q}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-f _ _ lab-isb}          x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-skip _ _}               x∈dst ()
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opt₂ _
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}     x∈dst () | opf₃ _
    
  Fmm[⇒] : Pred[⇒] (EvFₜ MM) (EvFₘ F-full)
  Fmm[⇒] = [$⇒]→₁[⇒] Fmm[$⇒]
  
  F[⇒]ld : {m : TCG.LabF} → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
    → Pred[⇒] (EvFₜ m) (EvFₘ F-ld)
  F[⇒]ld (here refl)                 = Frr[⇒]
  F[⇒]ld (there (here refl))         = Frw[⇒]
  F[⇒]ld (there (there (here refl))) = Frm[⇒]
  
  F[⇒]ff : {m : TCG.LabF} → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ [])
    → Pred[⇒] (EvFₜ m) (EvFₘ F-full)
  F[⇒]ff (here refl)                                         = Fwr[⇒]
  F[⇒]ff (there (here refl))                                 = Fwm[⇒]
  F[⇒]ff (there (there (here refl)))                         = Fmr[⇒]
  F[⇒]ff (there (there (there (here refl))))                 = Fmw[⇒]
  F[⇒]ff (there (there (there (there (here refl)))))         = Fmm[⇒]
