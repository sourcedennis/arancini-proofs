{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.RISCV using (arch-RISCV; RISCVExecution)
open import MapTCGtoRISCV using (RISCV-TCGRestricted)


module Proof.Mapping.TCGtoRISCV.Execution
  {dst : Execution {arch-RISCV}}
  {dst-rv : RISCVExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : RISCV-TCGRestricted dst-rv)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using () renaming (trans to ≡-trans)
open import Data.Empty using (⊥-elim)
-- open import Data.Product using (_,_)
-- open import Data.Sum using (inj₁; inj₂)
-- open import Data.List using (_∷_; [])
-- open import Data.List.Relation.Unary.Any using (here; there)
-- open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
-- open import Function using (_∘_; flip)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
-- -- Library imports
-- open import Dodo.Unary
-- open import Dodo.Binary hiding (REL)
-- -- Local imports
open import Helpers
open import MapTCGtoRISCV
open import Arch.RISCV as RISCV
open import Arch.TCG as TCG

open Δ.Defs

open RISCV-TCGRestricted dst-ok


-- # Backward Mapping of Relations


-- The (forward) mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ  || successful RMW
-- Rₐ         ↦  Rₐ         || failed RMW
--
-- F_RR   ↦  F_RR
-- F_RW   ↦  F_RW
-- F_RM   ↦  F_RM
-- F_WR   ↦  F_WR
-- F_WW   ↦  F_WW
-- F_WM   ↦  F_WM
-- F_MR   ↦  F_MR
-- F_MW   ↦  F_MW
-- F_MM   ↦  F_MM


open import Data.Bool using (Bool; true; false)

ev[⇐] : {x : EventRISCV} → (x∈dst : x ∈ events dst) → EventTCG
ev[⇐] {event-init uid loc val} x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid} x∈dst = event-skip uid tid
ev[⇐] {event-r uid tid loc val lab} x∈dst =
  -- many of the tag/annotation cases are impossible.
  -- we can still map them, and disprove them elsewhere.
  -- it makes some proofs easier.
  event-r uid tid loc val (lab[⇐] lab)
  where
  lab[⇐] : RISCV.LabR → TCG.LabR
  lab[⇐] (lab-r tag _) = lab-r tag
ev[⇐] {event-w uid tid loc val lab} x∈dst =
  -- many of the tag/annotation cases are impossible.
  event-w uid tid loc val (lab[⇐] lab)
  where
  lab[⇐] : RISCV.LabW → TCG.LabW
  lab[⇐] (lab-w tag _) = lab-w tag
ev[⇐] {event-f uid tid lab} x∈dst =
  event-f uid tid (lab[⇐] lab)
  where
  ac[⇐] : RISCV.AccessClass → TCG.AccessClass
  ac[⇐] 𝐴R = 𝐴R
  ac[⇐] 𝐴W = 𝐴W
  ac[⇐] 𝐴M = 𝐴M

  lab[⇐] : RISCV.LabF → TCG.LabF
  lab[⇐] (x 𝐹 y) = (ac[⇐] x) 𝐹 (ac[⇐] y)
  lab[⇐] TSO = MM -- impossible case


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
uid[⇐] {_}                     x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                     x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_} {event-r _ _ _ _ _} x∈dst has-uid-r    = has-uid-r
uid[⇐] {_} {event-w _ _ _ _ _} x∈dst has-uid-w    = has-uid-w
uid[⇐] {_} {event-f _ _ _}     x∈dst has-uid-f    = has-uid-f

uid[$⇒] : Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}  x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}    x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-uid-r    = has-uid-r
uid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-uid-w    = has-uid-w
uid[$⇒] {_} {event-f _ _ _}     x∈dst has-uid-f    = has-uid-f


tid[⇐] : Pred[⇐]² (HasTid tid)
tid[⇐] {_}                     x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} {event-r _ _ _ _ _} x∈dst has-tid-r    = has-tid-r
tid[⇐] {_} {event-w _ _ _ _ _} x∈dst has-tid-w    = has-tid-w
tid[⇐] {_} {event-f _ _ _}     x∈dst has-tid-f    = has-tid-f

tid[$⇒] : Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}    x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-tid-r    = has-tid-r
tid[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-tid-w    = has-tid-w
tid[$⇒] {_} {event-f _ _ _}     x∈dst has-tid-f    = has-tid-f


loc[⇐] : Pred[⇐]² (HasLoc loc)
loc[⇐] {_}                     x∈dst has-loc-init = has-loc-init
loc[⇐] {_} {event-r _ _ _ _ _} x∈dst has-loc-r    = has-loc-r
loc[⇐] {_} {event-w _ _ _ _ _} x∈dst has-loc-w    = has-loc-w

loc[$⇒] : Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}  x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-loc-r    = has-loc-r
loc[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-loc-w    = has-loc-w


val[⇐] : Pred[⇐]² (HasVal val)
val[⇐] {_}                     x∈dst has-val-init = has-val-init
val[⇐] {_} {event-r _ _ _ _ _} x∈dst has-val-r    = has-val-r
val[⇐] {_} {event-w _ _ _ _ _} x∈dst has-val-w    = has-val-w

val[$⇒] : Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}  x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-r _ _ _ _ _} x∈dst has-val-r    = has-val-r
val[$⇒] {_} {event-w _ _ _ _ _} x∈dst has-val-w    = has-val-w


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}  x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-skip _ _}    x∈dst ()
Init[$⇒] {event-r _ _ _ _ _} x∈dst ()
Init[$⇒] {event-w _ _ _ _ _} x∈dst ()
Init[$⇒] {event-f _ _ _}     x∈dst ()


Wₜ[⇐] : Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] {_} {event-init _ _ _}            x∈dst (ev-init is-tag) = ev-init is-tag
Wₜ[⇐] {_} {event-w _ _ _ _ (lab-w _ _)} x∈dst (ev-w is-tag)    = ev-w is-tag

Wₜ[$⇒] : Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}            x∈dst (ev-init is-tag) = ev-init is-tag
Wₜ[$⇒] {_} {event-w _ _ _ _ (lab-w _ _)} x∈dst (ev-w is-tag)    = ev-w is-tag


Rₜ[⇐] : Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {_} {event-r _ _ _ _ (lab-r _ _)} x∈dst (ev-r is-tag) = ev-r is-tag

Rₜ[$⇒] : Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-r _ _ _ _ (lab-r _ _)} x∈dst (ev-r is-tag) = ev-r is-tag


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

  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Product using (_,_)
  open import Function using (flip; _∘_)
  open import Burrow.Framework.Mapping.Definitions δ
  open import Burrow.Framework.WellFormed ψ using (rmw[⇒]; rel[$⇒]; rel[⇐])
  open RISCVExecution
  open Δ.Consistency δ using (rmwˡ-r; rmwʳ-w)
  open import Dodo.Binary


  -- # Map the RISCVExecution to a TCGExecution

  -- Basically, our `si` is as empty as it gets. That is, every event is only
  -- generated by the same instruction as itself.
  
  src-si : Rel₀ EventTCG
  src-si = ⦗ events src ⦘

  src-si-internal : src-si ⊆₂ po src ∪₂ flip (po src) ∪₂ ⦗ events src ⦘
  src-si-internal = ⊆: λ{_ _ → opf₃}

  src-si-refl : Reflexive (filter-rel (events src) src-si)
  src-si-refl {with-pred xˢ x∈src} = (refl , x∈src)

  src-si-sym : Symmetric src-si
  src-si-sym (refl , x∈src) = (refl , x∈src)

  src-si-trans : Transitive src-si
  src-si-trans (x≡y@refl , x∈src) (y≡z@refl , _) = (≡-trans x≡y y≡z , x∈src)

  src-tex : TCGExecution src
  src-tex =
    record {
      si          = src-si
    ; si-internal = src-si-internal
    ; si-refl     = λ {x} → src-si-refl {x}
    ; si-sym      = src-si-sym
    ; si-trans    = src-si-trans
    }


--   Rₜ[⇒]A : Pred[⇒] (EvRₜ trmw) EvA
--   Rₜ[⇒]A x∈src = Rₐ⇒A dst-ok (events[⇒] x∈src) ∘ Rₜ[⇒] x∈src

--   Wₜ[⇒]L : Pred[⇒] (EvWₜ trmw) EvL
--   Wₜ[⇒]L x∈src = Wₐ⇒L dst-ok (events[⇒] x∈src) ∘ Wₜ[⇒] x∈src

--   rmw[⇒]amo : Rel[⇒] (rmw src) (amo dst-a8)
--   rmw[⇒]amo x∈src y∈src = rmw⇒amo dst-ok dst-wf ∘ (rmw[⇒] x∈src y∈src)
  
--   rmw[⇒]amo-al : Rel[⇒] (rmw src) (⦗ EvA ⦘ ⨾ amo dst-a8 ⨾ ⦗ EvL ⦘)
--   rmw[⇒]amo-al x∈src y∈src rmw[xy] =
--     let dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
--         x-a = Rₐ⇒A dst-ok (events[⇒] x∈src) (rmwˡ-r dst-wf (take-dom (rmw dst) dst-rmw[xy]))
--         y-l = Wₐ⇒L dst-ok (events[⇒] y∈src) (rmwʳ-w dst-wf (take-codom (rmw dst) dst-rmw[xy]))
--     in (refl , x-a) ⨾[ _ ]⨾ rmw[⇒]amo x∈src y∈src rmw[xy] ⨾[ _ ]⨾ (refl , y-l)
  
  R₌[$⇒] : Pred[$⇒] (EvR₌ loc val (lab-r tmov)) (EvR₌ loc val (lab-r tmov ann-none))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r .tmov ann-none)} x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r .tmov ann-rel)} x∈dst ev-r =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {event-r _ _ _ _ (lab-r .tmov (true ⦂ann⦂ _))} x∈dst ev-r =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  R₌[⇒] : Pred[⇒] (EvR₌ loc val (lab-r tmov)) (EvR₌ loc val (lab-r tmov ann-none))
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  R₌[$⇒]sc : Pred[$⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-r trmw ann-acqrel))
  R₌[$⇒]sc {_} {_} {event-r _ _ _ _ (lab-r .trmw ann-acqrel)}      x∈dst ev-r = ev-r
  -- impossible cases
  R₌[$⇒]sc {_} {_} {event-r _ _ _ _ (lab-r .trmw (false ⦂ann⦂ _))} x∈dst ev-r =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒]sc {_} {_} {event-r _ _ _ _ (lab-r .trmw ann-acq)}         x∈dst ev-r =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  R₌[⇒]sc : Pred[⇒] (EvR₌ loc val (lab-r trmw)) (EvR₌ loc val (lab-r trmw ann-acqrel))
  R₌[⇒]sc = [$⇒]→₁[⇒] R₌[$⇒]sc
    

  W₌[$⇒] : Pred[$⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov ann-none))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w .tmov ann-none)} x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w .tmov ann-rel)}        x∈dst ev-w =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {event-w _ _ _ _ (lab-w .tmov (true ⦂ann⦂ _))} x∈dst ev-w =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  W₌[⇒] : Pred[⇒] (EvW₌ loc val (lab-w tmov)) (EvW₌ loc val (lab-w tmov ann-none))
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  W₌[$⇒]sc : Pred[$⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-w trmw ann-acqrel))
  W₌[$⇒]sc {_} {_} {event-w _ _ _ _ (lab-w .trmw ann-acqrel)}      x∈dst ev-w = ev-w
  -- impossible cases
  W₌[$⇒]sc {_} {_} {event-w _ _ _ _ (lab-w .trmw (false ⦂ann⦂ _))} x∈dst ev-w =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒]sc {_} {_} {event-w _ _ _ _ (lab-w .trmw ann-acq)}         x∈dst ev-w =
    ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  W₌[⇒]sc : Pred[⇒] (EvW₌ loc val (lab-w trmw)) (EvW₌ loc val (lab-w trmw ann-acqrel))
  W₌[⇒]sc = [$⇒]→₁[⇒] W₌[$⇒]sc


  -- Map fences. RR / RW / RM / WR / WW / WM / MR / MW / MM

  Fₜ[$⇒] : {t : TCG.LabF} → Pred[$⇒] (EvFₜ t) (EvFₜ (rule-labf t))
  Fₜ[$⇒] {_} {event-f _ _ RR} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ RW} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ RM} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ WR} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ WW} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ WM} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ MR} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ MW} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ MM} x∈dst ev-f = ev-f
  Fₜ[$⇒] {_} {event-f _ _ TSO} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  
  Fₜ[⇒] : {t : TCG.LabF} → Pred[⇒] (EvFₜ t) (EvFₜ (rule-labf t))
  Fₜ[⇒] = [$⇒]→₁[⇒] Fₜ[$⇒]
