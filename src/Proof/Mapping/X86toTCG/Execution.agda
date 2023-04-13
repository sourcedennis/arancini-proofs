{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import Arch.Mixed using (MixedExecution)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Execution
  {dst : Execution {arch-TCG}}
  {dst-tex : MixedExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst-tex)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Sum as Sum using ([_,_])
open import Data.Product as Prod using (_,_)
open import Function using (flip)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
-- Library imports
open import Dodo.Binary
-- Local imports
open import Helpers
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
-- we only have `MM ↦ F`. The others (MR, MW) don't occur. we disprove them elsewhere.
ev[⇐] {event-f uid tid (𝐴M 𝐹 _)}    x∈dst = event-f uid tid lab-f
-- we only have `RM ↦ skip` and `WW ↦ skip`. The others (MR, MW) don't occur. we disprove
-- them elsewhere. Itt makes the proofs easier.
ev[⇐] {event-f uid tid (𝐴R 𝐹 _)} x∈dst = event-skip uid tid
ev[⇐] {event-f uid tid (𝐴W 𝐹 _)} x∈dst = event-skip uid tid

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
uid[⇐] {_}                        x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                        x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_}                        x∈dst has-uid-r    = has-uid-r
uid[⇐] {_}                        x∈dst has-uid-w    = has-uid-w
uid[⇐] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst has-uid-f    = has-uid-f
uid[⇐] {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst has-uid-f    = has-uid-skip
uid[⇐] {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst has-uid-f    = has-uid-skip

uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}     x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}       x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ _}    x∈dst has-uid-r    = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ _}    x∈dst has-uid-w    = has-uid-w
uid[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst has-uid-f    = has-uid-f
uid[$⇒] {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst has-uid-skip = has-uid-f
uid[$⇒] {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst has-uid-skip = has-uid-f


tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_}                        x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_}                        x∈dst has-tid-r    = has-tid-r
tid[⇐] {_}                        x∈dst has-tid-w    = has-tid-w
tid[⇐] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst has-tid-f    = has-tid-f
tid[⇐] {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst has-tid-f    = has-tid-skip
tid[⇐] {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst has-tid-f    = has-tid-skip

tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}       x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ _}    x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ _}    x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst has-tid-f    = has-tid-f
tid[$⇒] {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst has-tid-skip = has-tid-f
tid[$⇒] {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst has-tid-skip = has-tid-f


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init = has-loc-init
loc[⇐] x∈dst has-loc-r    = has-loc-r
loc[⇐] x∈dst has-loc-w    = has-loc-w

loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}  x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-loc-w    = has-loc-w
-- impossible cases
loc[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init = has-val-init
val[⇐] x∈dst has-val-r    = has-val-r
val[⇐] x∈dst has-val-w    = has-val-w

val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}  x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-val-w    = has-val-w
-- impossible cases
val[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐]                                 x∈dst (ev-init refl) = ev-init refl
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl

Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}          x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _)} x∈dst (ev-w refl)    = ev-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r refl) = ev-r refl

Rₜ[$⇒] : Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r _)} x∈dst (ev-r refl) = ev-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()


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
  open TCG.Properties dst-tex dst-wf
  open MixedExecution dst-tex
  open Δ.Consistency δ using (ev[⇐$]eq)


  F[$⇒] : Pred[$⇒] EvF (EvFₜ MM)
  F[$⇒] {event-f _ _ MM} x∈dst ev-f = ev-f
  -- impossible cases
  F[$⇒] {event-f _ _ MR} x∈dst ev-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event-f _ _ MW} x∈dst ev-f = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  F[⇒] : Pred[⇒] EvF (EvFₜ MM)
  F[⇒] = [$⇒]→₁[⇒] F[$⇒]


  R₌[$⇒] : Pred[$⇒] (EvR₌ loc val (X86.lab-r tag)) (EvR₌ loc val (TCG.lab-r tag))
  R₌[$⇒] {_} {_} {_} {event-r _ _ _ _ (lab-r _)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst ()
  R₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst ()
  R₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()
  
  R₌[⇒] : Pred[⇒] (EvR₌ loc val (X86.lab-r tag)) (EvR₌ loc val (TCG.lab-r tag))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (X86.lab-w tag)) (EvW₌ loc val (TCG.lab-w tag))
  W₌[$⇒] {_} {_} {_} {event-w _ _ _ _ (lab-w _)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴R 𝐹 _)} x∈dst ()
  W₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴W 𝐹 _)} x∈dst ()
  W₌[$⇒] {_} {_} {_} {event-f _ _ (𝐴M 𝐹 _)} x∈dst ()
  
  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tag)) (EvW₌ loc val (lab-w tag))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]
