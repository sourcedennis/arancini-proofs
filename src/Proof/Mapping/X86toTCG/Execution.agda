{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Execution
  {dst : Execution {arch-TCG}}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Local imports
open import MapX86toTCG
open import Arch.TCG as TCG
open import Arch.X86 as X86

open Δ.Defs


dst-consistent = TCG-X86Restricted.consistent dst-ok


-- # Backward Mapping of Relations

-- Instruction mapping:
--
-- RMOV   ↦ LD;F_LD_M
-- WMOV   ↦ F_ST_ST;ST
-- RMW    ↦ RMW
-- MFENCE ↦ F_SC
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)             ↦ Rᵣ(x,v);F_RM
-- W(x,v)              ↦ F_WW;Wᵣ(x,v)
-- Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;Wₗ(x,v')  || successful RMW
-- Rₗ(x,v)             ↦ Rₗ(x,v)               || failed RMW
-- F                   ↦ F_SC


LabR[⇐] : TCG.LabR → X86.LabR
LabR[⇐] (lab-r tag) = lab-r tag

LabW[⇐] : TCG.LabW → X86.LabW
LabW[⇐] (lab-w tag) = lab-w tag


ev[⇐] : {x : EventTCG}
  → (x∈dst : x ∈ events dst)
    ------------------------
  → EventX86
ev[⇐] {event-init uid loc val}      x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}          x∈dst = event-skip uid tid
ev[⇐] {event-r uid tid loc val lab} x∈dst = event-r uid tid loc val (LabR[⇐] lab)
ev[⇐] {event-w uid tid loc val lab} x∈dst = event-w uid tid loc val (LabW[⇐] lab)
ev[⇐] {event-f uid tid RM}          x∈dst = event-skip uid tid
ev[⇐] {event-f uid tid WW}          x∈dst = event-skip uid tid
ev[⇐] {event-f uid tid SC}          x∈dst = event-f uid tid lab-f
-- impossible cases
ev[⇐] {event-f uid tid RR}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid RW}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid WR}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid WM}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid M?}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid ACQ} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event-f uid tid REL} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


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
uid[⇐] {_}                  x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                  x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_}                  x∈dst has-uid-r    = has-uid-r
uid[⇐] {_}                  x∈dst has-uid-w    = has-uid-w
uid[⇐] {_} {event-f _ _ RM} x∈dst has-uid-f    = has-uid-skip
uid[⇐] {_} {event-f _ _ WW} x∈dst has-uid-f    = has-uid-skip
uid[⇐] {_} {event-f _ _ SC} x∈dst has-uid-f    = has-uid-f
-- impossible cases
uid[⇐] {_} {event-f _ _ RR}  x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ RW}  x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ WR}  x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ WM}  x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ M?}  x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ ACQ} x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event-f _ _ REL} x∈dst has-uid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}  x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}    x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-uid-r    = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-uid-w    = has-uid-w
uid[$⇒] {_} {event-f _ _ RM}    x∈dst has-uid-skip = has-uid-f
uid[$⇒] {_} {event-f _ _ WW}    x∈dst has-uid-skip = has-uid-f
uid[$⇒] {_} {event-f _ _ SC}    x∈dst has-uid-f    = has-uid-f
-- impossible cases
uid[$⇒] {_} {event-f _ _ RR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ RW}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ WR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ WM}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ M?}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ ACQ} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event-f _ _ REL} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_}                  x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_}                  x∈dst has-tid-r    = has-tid-r
tid[⇐] {_}                  x∈dst has-tid-w    = has-tid-w
tid[⇐] {_} {event-f _ _ RM} x∈dst has-tid-f    = has-tid-skip
tid[⇐] {_} {event-f _ _ WW} x∈dst has-tid-f    = has-tid-skip
tid[⇐] {_} {event-f _ _ SC} x∈dst has-tid-f    = has-tid-f
-- impossible cases
tid[⇐] {_} {event-f _ _ RR}  x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ RW}  x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ WR}  x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ WM}  x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ M?}  x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ ACQ} x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event-f _ _ REL} x∈dst has-tid-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}    x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-f _ _ RM}    x∈dst has-tid-skip = has-tid-f
tid[$⇒] {_} {event-f _ _ WW}    x∈dst has-tid-skip = has-tid-f
tid[$⇒] {_} {event-f _ _ SC}    x∈dst has-tid-f    = has-tid-f
-- impossible cases
tid[$⇒] {_} {event-f _ _ RR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ RW}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ WR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ WM}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ M?}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ ACQ} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event-f _ _ REL} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init = has-loc-init
loc[⇐] x∈dst has-loc-r    = has-loc-r
loc[⇐] x∈dst has-loc-w    = has-loc-w

loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}  x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-loc-w    = has-loc-w
-- impossible cases
loc[$⇒] {_} {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init = has-val-init
val[⇐] x∈dst has-val-r    = has-val-r
val[⇐] x∈dst has-val-w    = has-val-w

val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}  x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-val-w    = has-val-w
-- impossible cases
val[$⇒] {_} {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-f _ _ RR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ RW}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ WR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ WM}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ MR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ MW}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ MM}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ ACQ} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event-f _ _ REL} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐]                                 x∈dst (ev-init refl) = ev-init refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl

Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}          x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-r _ _ _ _ _} x∈dst ()
Wₜ[$⇒] {_} {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r refl) = ev-r refl

Rₜ[$⇒] : Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-init _ _ _}  x∈dst ()
Rₜ[$⇒] {_} {event-w _ _ _ _ _} x∈dst ()
Rₜ[$⇒] {_} {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


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


  R₌[$⇒] : Pred[$⇒] (EvR₌ loc val (X86.lab-r tag)) (EvR₌ loc val (TCG.lab-r tag))
  R₌[$⇒] {_} {_} {_} {event-r _ _ _ _ (lab-r _)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-f _ _ RR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ RW}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ WR}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ WM}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ M?}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ ACQ} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event-f _ _ REL} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  R₌[⇒] : Pred[⇒] (EvR₌ loc val (X86.lab-r tag)) (EvR₌ loc val (TCG.lab-r tag))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (X86.lab-w tag)) (EvW₌ loc val (TCG.lab-w tag))
  W₌[$⇒] {_} {_} {_} {event-w _ _ _ _ (lab-w _)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tag)) (EvW₌ loc val (lab-w tag))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]
  

  F[$⇒] : Pred[$⇒] EvF (EvFₜ SC)
  F[$⇒] {event-f _ _ SC} x∈dst ev-f = ev-f
  -- impossible cases
  F[$⇒] {event-f _ _ RR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ RW}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ WR}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ WM}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ M?}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ ACQ}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ REL}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  F[⇒] : Pred[⇒] EvF (EvFₜ SC)
  F[⇒] = [$⇒]→₁[⇒] F[$⇒]
