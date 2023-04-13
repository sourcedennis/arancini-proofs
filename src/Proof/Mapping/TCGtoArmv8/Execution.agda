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
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (inj₁; inj₂)
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
ev[⇐] {event-r uid tid loc val lab} x∈dst = event-r uid tid loc val (lab[⇐] lab)
  where
  -- only `lab-r tmov` and `lab-a trmw` are possible.
  -- we map all, because it makes the proofs easier. (and prove their absence elsewhere)
  lab[⇐] : Armv8.LabR → TCG.LabR
  lab[⇐] (lab-r tag) = lab-r tag
  lab[⇐] (lab-a tag) = lab-r tag
  lab[⇐] lab-q       = lab-r tmov
ev[⇐] {event-w uid tid loc val lab} x∈dst =
  event-w uid tid loc val (lab[⇐] lab)
  where
  -- only `lab-w tmov` and `lab-l trmw` are possible
  lab[⇐] : Armv8.LabW → TCG.LabW
  lab[⇐] (lab-w tag) = lab-w tag
  lab[⇐] (lab-l tag) = lab-w tag
ev[⇐] x@{event-f uid tid lab} x∈dst = event-f uid tid (lab[⇐] lab refl)
  where
  lab[⇐] : (l : Armv8.LabF) → l ≡ lab → TCG.LabF
  lab[⇐] (lab-f F-full) refl with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  ... | (opt₁ _) = WR
  ... | (opt₂ _) = WM
  ... | (opt₃ _) = MR
  ... | (opt₄ _) = MW
  ... | (opf₅ _) = MM
  lab[⇐] (lab-f F-ld) refl with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  ... | (opt₁ _) = RR
  ... | (opt₂ _) = RW
  ... | (opf₃ _) = RM
  lab[⇐] (lab-f F-st) _ = WW
  lab[⇐] lab-isb      _ = MM -- impossible


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
uid[⇐] {_} x∈dst has-uid-r    = has-uid-r
uid[⇐] {_} x∈dst has-uid-w    = has-uid-w
uid[⇐] {_} x∈dst has-uid-f    = has-uid-f

uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}  x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}    x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-uid-r    = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-uid-w    = has-uid-w
uid[$⇒] {_} {event-f _ _ _}     x∈dst has-uid-f    = has-uid-f

    
tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_} x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} x∈dst has-tid-r    = has-tid-r
tid[⇐] {_} x∈dst has-tid-w    = has-tid-w
tid[⇐] {_} x∈dst has-tid-f    = has-tid-f

tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}    x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-f _ _ _}     x∈dst has-tid-f    = has-tid-f


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init = has-loc-init
loc[⇐] x∈dst has-loc-r    = has-loc-r
loc[⇐] x∈dst has-loc-w    = has-loc-w

loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}  x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-loc-w    = has-loc-w


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init = has-val-init
val[⇐] x∈dst has-val-r    = has-val-r
val[⇐] x∈dst has-val-w    = has-val-w

val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}  x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-val-w    = has-val-w


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] {_} {_}                         x∈dst (ev-init eq) = ev-init eq
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w eq)    = ev-w eq
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-l _)} x∈dst (ev-w eq)    = ev-w eq

Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}          x∈dst (ev-init eq) = ev-init eq
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w eq)    = ev-w eq
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-l _)} x∈dst (ev-w eq)    = ev-w eq


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r eq) = ev-r eq
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-a _)} x∈dst (ev-r eq) = ev-r eq
Rₜ[⇐] {_} {event-r _ _ _ _ lab-q}     x∈dst (ev-r eq) = ev-r eq

Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r eq) = ev-r eq
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-a _)} x∈dst (ev-r eq) = ev-r eq
Rₜ[$⇒] {_} {event-r _ _ _ _ lab-q}     x∈dst (ev-r eq) = ev-r eq


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
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r .tmov)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-a .tmov)} x∈dst ev-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ lab-q}         x∈dst ev-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  R₌[⇒] : Pred[⇒] (EvR₌ loc val (lab-r tmov)) (EvR₌ loc val (lab-r tmov))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  R₌[$⇒]A : Pred[$⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-a trmw))
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ (lab-a .trmw)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒]A {_} {_} {event-r _ _ _ _ (lab-r .trmw)} x∈dst ev-r = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  R₌[⇒]A : Pred[⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-a trmw))
  R₌[⇒]A = [$⇒]→₁[⇒] R₌[$⇒]A
    

  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w .tmov)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-l .tmov)} x∈dst ev-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  W₌[$⇒]L : Pred[$⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-l trmw))
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-l .trmw)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒]L {_} {_} {event-w _ _ _ _ (lab-w .trmw)} x∈dst ev-w = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  W₌[⇒]L : Pred[⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-l trmw))
  W₌[⇒]L = [$⇒]→₁[⇒] W₌[$⇒]L


  -- Map fences. RR / RW / RM / WR / WW / WM / MR / MW / MM / SC
  --
  -- RR / RW / RM                → F-ld
  -- WW                          → F-st
  -- WR / WM / MR / MW / MM / SC → F-full

  Frr[$⇒] : Pred[$⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ = ev-f
  -- impossible cases
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₄ _
  Frr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₅ _
    
  Frr[⇒] : Pred[⇒] (EvFₜ RR) (EvFₘ F-ld)
  Frr[⇒] = [$⇒]→₁[⇒] Frr[$⇒]


  Frw[$⇒] : Pred[$⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ = ev-f
  -- impossible cases
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₄ _
  Frw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₅ _
    
  Frw[⇒] : Pred[⇒] (EvFₜ RW) (EvFₘ F-ld)
  Frw[⇒] = [$⇒]→₁[⇒] Frw[$⇒]
  

  Frm[$⇒] : Pred[$⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst x-f = ev-f
  -- impossible cases
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst x-f with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₄ _
  Frm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₅ _
    
  Frm[⇒] : Pred[⇒] (EvFₜ RM) (EvFₘ F-ld)
  Frm[⇒] = [$⇒]→₁[⇒] Frm[$⇒]


  Fww[$⇒] : Pred[$⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[$⇒] {event-f _ _ (lab-f F-st)} x∈dst ev-f = ev-f
  -- impossible cases
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opt₄ _
  Fww[$⇒] {event-f _ _ (lab-f F-full)} x∈dst () | opf₅ _
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fww[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
    
  Fww[⇒] : Pred[⇒] (EvFₜ WW) (EvFₘ F-st)
  Fww[⇒] = [$⇒]→₁[⇒] Fww[$⇒]
  

  Fwr[$⇒] : Pred[$⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fwr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  
  Fwr[⇒] : Pred[⇒] (EvFₜ WR) (EvFₘ F-full)
  Fwr[⇒] = [$⇒]→₁[⇒] Fwr[$⇒]


  Fwm[$⇒] : Pred[$⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fwm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  
  Fwm[⇒] : Pred[⇒] (EvFₜ WM) (EvFₘ F-full)
  Fwm[⇒] = [$⇒]→₁[⇒] Fwm[$⇒]


  Fmr[$⇒] : Pred[$⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmr[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  
  Fmr[⇒] : Pred[⇒] (EvFₜ MR) (EvFₘ F-full)
  Fmr[⇒] = [$⇒]→₁[⇒] Fmr[$⇒]


  Fmw[$⇒] : Pred[$⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmw[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  
  Fmw[⇒] : Pred[⇒] (EvFₜ MW) (EvFₘ F-full)
  Fmw[⇒] = [$⇒]→₁[⇒] Fmw[$⇒]


  Fmm[$⇒] : Pred[$⇒] (EvFₜ MM) (EvFₘ F-full)
  Fmm[$⇒] {event-f _ _ (lab-f F-full)} x∈dst _ = ev-f
  -- impossible cases
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ org-ld-def (x∈dst , ev-f)
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opt₂ _
  Fmm[$⇒] {event-f _ _ (lab-f F-ld)}   x∈dst () | opf₃ _
  Fmm[$⇒] {event-f _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
  
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
