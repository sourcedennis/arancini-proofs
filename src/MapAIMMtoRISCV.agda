{-# OPTIONS --safe #-}


module MapAIMMtoRISCV where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Function using (id)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; ∃-syntax)
open import Data.Empty using (⊥)
open import Data.List using (_∷_; [])
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary hiding (REL)
open import Burrow.Template.Mapping as Δ
-- Local imports: Architectures
open import Arch.AIMM as AIMM
open import Arch.RISCV as RISCV


-- Mapping - AIMM ⇒ RISCV
--
-- Instruction mapping:
--
-- LD       ↦  LD
-- ST       ↦  ST
-- RMW      ↦  RMW_SC
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
--
--
-- Corresponding event mapping:
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

rule-ac : AIMM.AccessClass → RISCV.AccessClass
rule-ac 𝐴R = 𝐴R
rule-ac 𝐴W = 𝐴W
rule-ac 𝐴M = 𝐴M

rule-labf : AIMM.LabF → RISCV.LabF
rule-labf (x 𝐹 y) = (rule-ac x) 𝐹 (rule-ac y)

record AIMM⇒RISCV
    (src : Execution {arch-AIMM})
    {dst : Execution {arch-RISCV}}
    (dst-rv : RISCVExecution dst) : Set where
    
  open Δ.Defs
  open AIMM.LabR
  open AIMM.LabW
  open RISCVExecution dst-rv

  field
    -- Instrs: LD ↦ LDR
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
    rule-ld : ∀ {a : EventAIMM} {x : Location} {v : Value}
      → EvR₌ x v (lab-r tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov ann-none) a')

    -- Instrs: ST ↦ STR
    -- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
    rule-st : ∀ {a : EventAIMM} {x : Location} {v : Value}
      → EvW₌ x v (lab-w tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov ann-none) a')


    -- Instrs: RMW        ↦  RMW_SC
    -- Events: Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ  || successful RMW
    --         Rₐ         ↦  Rₐ         || failed RMW

    rule-rmw-dom : ∀ {a : EventAIMM} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw ann-acqrel) a')
      
    rule-rmw-codom : ∀ {a : EventAIMM} {x : Location} {v : Value}
      → EvW₌ x v (lab-w trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w trmw ann-acqrel) a')

    rule-rmw-ok : ∀ {a b : EventAIMM} {x : Location} {v₁ v₂ : Value}
      → EvR₌ x v₁ (lab-r trmw) a
      → EvW₌ x v₂ (lab-w trmw) b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × EvR₌ x v₁ (lab-r trmw ann-acqrel) a' × EvW₌ x v₂ (lab-w trmw ann-acqrel) b')

    rule-rmw-fail : ∀ {a : EventAIMM} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → a ∉ dom (rmw src)
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw ann-acqrel) a' × a' ∉ dom (rmw dst))

    -- Both instrs and events. Basically, the fences remain the same.
    -- F_RR   ↦  F_RR
    -- F_RW   ↦  F_RW
    -- F_RM   ↦  F_RM
    -- F_WR   ↦  F_WR
    -- F_WW   ↦  F_WW
    -- F_WM   ↦  F_WM
    -- F_MR   ↦  F_MR
    -- F_MW   ↦  F_MW
    -- F_MM   ↦  F_MM

    rule-f : ∀ {a : EventAIMM} {f : AIMM.LabF}
      → EvFₜ f a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvFₜ (rule-labf f) a')


private
  variable
    uid  : UniqueId
    tid  : ThreadId
    -- mode : F-mode
    loc  : Location
    val  : Value


-- RISCV programs mapped from AIMM can only contain these events
data IsRISCVEventAIMM : Pred₀ EventRISCV where
  ev-init : IsRISCVEventAIMM (event-init uid loc val)
  ev-skip : IsRISCVEventAIMM (event-skip uid tid)
  -- read events produced from relaxed read instructions
  --   (i.e., no AMO/SC instr, no acq/rel annotations)
  ev-rᵣ   : IsRISCVEventAIMM (event-r uid tid loc val (lab-r tmov ann-none))
  -- write events produced from relaxed write instructions
  --   (i.e., no AMO/SC instr, no acq/rel annotations)
  ev-wᵣ   : IsRISCVEventAIMM (event-w uid tid loc val (lab-w tmov ann-none))
  -- read events produced by AMO instructions with acq/rel annotations
  ev-rₐ   : IsRISCVEventAIMM (event-r uid tid loc val (lab-r trmw ann-acqrel))
  -- write events produced by AMO instructions with acq/rel annotations
  ev-wₐ   : IsRISCVEventAIMM (event-w uid tid loc val (lab-w trmw ann-acqrel))
  -- basically, we can produce any memory fence. we *don't* produce TSO fences.
  ev-f    : (x y : RISCV.AccessClass) → IsRISCVEventAIMM (event-f uid tid (x 𝐹 y))


record RISCV-AIMMRestricted {ex : Execution {arch-RISCV}} (rv : RISCVExecution ex) : Set₁ where
  open Δ.Restrict ex
  open RISCV.Relations rv
  
  field
    consistent : IsRISCVConsistent
    
    ev-bound : events ⊆₁ IsRISCVEventAIMM


-- # Helpers

module _ {ex : Execution {arch-RISCV}} {rv : RISCVExecution ex} (ex-res : RISCV-AIMMRestricted rv) where

  open Execution ex
  open RISCV-AIMMRestricted ex-res


  ¬ev-bound : {ev : EventRISCV}
    → ev ∈ events
    → ¬ (IsRISCVEventAIMM ev)
    → ⊥
  ¬ev-bound ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply ev-bound ev∈ex)


  module _ (wf : WellFormed ex) where
  
    open WellFormed wf


    po-bound : po ⊆₂ IsRISCVEventAIMM ×₂ IsRISCVEventAIMM
    po-bound = ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ po-elements)) (×₂-lift ev-bound ev-bound)

    rf-bound : rf ⊆₂ IsRISCVEventAIMM ×₂ IsRISCVEventAIMM
    rf-bound = ⊆₂-trans (×₂-lift-udr rf-elements) (×₂-lift ev-bound ev-bound)

    co-bound : co ⊆₂ IsRISCVEventAIMM ×₂ IsRISCVEventAIMM
    co-bound = ⊆₂-trans (×₂-lift-udr co-elements) (×₂-lift ev-bound ev-bound)

    rmw-bound : rmw ⊆₂ IsRISCVEventAIMM ×₂ IsRISCVEventAIMM
    rmw-bound = ⊆₂-trans rmw-def (⊆₂-trans imm-⊆₂ po-bound)
