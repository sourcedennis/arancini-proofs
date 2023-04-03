{-# OPTIONS --safe #-}


module MapTCGtoRISCV where

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
open import Arch.TCG as TCG
open import Arch.RISCV as RISCV


-- Mapping - TCG ⇒ RISCV
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

rule-ac : TCG.AccessClass → RISCV.AccessClass
rule-ac 𝐴R = 𝐴R
rule-ac 𝐴W = 𝐴W
rule-ac 𝐴M = 𝐴M

rule-labf : TCG.LabF → RISCV.LabF
rule-labf (x 𝐹 y) = (rule-ac x) 𝐹 (rule-ac y)

record TCG⇒RISCV
    (src : Execution {arch-TCG})
    {dst : Execution {arch-RISCV}}
    (dst-rv : RISCVExecution dst) : Set where
    
  open Δ.Defs
  open TCG.LabR
  open TCG.LabW
  open RISCVExecution dst-rv

  field
    -- Instrs: LD ↦ LDR
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
    rule-ld : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov ann-none) a')

    -- Instrs: ST ↦ STR
    -- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
    rule-st : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvW₌ x v (lab-w tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov ann-none) a')


    -- Instrs: RMW        ↦  RMW_SC
    -- Events: Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ  || successful RMW
    --         Rₐ         ↦  Rₐ         || failed RMW

    rule-rmw-dom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw ann-acqrel) a')
      
    rule-rmw-codom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvW₌ x v (lab-w trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w trmw ann-acqrel) a')

    rule-rmw-ok : ∀ {a b : EventTCG} {x : Location} {v₁ v₂ : Value}
      → EvR₌ x v₁ (lab-r trmw) a
      → EvW₌ x v₂ (lab-w trmw) b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × EvR₌ x v₁ (lab-r trmw ann-acqrel) a' × EvW₌ x v₂ (lab-w trmw ann-acqrel) b')

    rule-rmw-fail : ∀ {a : EventTCG} {x : Location} {v : Value}
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

    rule-f : ∀ {a : EventTCG} {f : TCG.LabF}
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


-- RISCV programs mapped from TCG can only contain these events
data IsRISCVEventTCG : Pred₀ EventRISCV where
  ev-init : IsRISCVEventTCG (event-init uid loc val)
  ev-skip : IsRISCVEventTCG (event-skip uid tid)
  -- read events produced from relaxed read instructions
  --   (i.e., no AMO/SC instr, no acq/rel annotations)
  ev-rᵣ   : IsRISCVEventTCG (event-r uid tid loc val (lab-r tmov ann-none))
  -- write events produced from relaxed write instructions
  --   (i.e., no AMO/SC instr, no acq/rel annotations)
  ev-wᵣ   : IsRISCVEventTCG (event-w uid tid loc val (lab-w tmov ann-none))
  -- read events produced by AMO instructions with acq/rel annotations
  ev-rₐ   : IsRISCVEventTCG (event-r uid tid loc val (lab-r trmw ann-acqrel))
  -- write events produced by AMO instructions with acq/rel annotations
  ev-wₐ   : IsRISCVEventTCG (event-w uid tid loc val (lab-w trmw ann-acqrel))
  -- basically, we can produce any memory fence. we *don't* produce TSO fences.
  ev-f    : (x y : RISCV.AccessClass) → IsRISCVEventTCG (event-f uid tid (x 𝐹 y))


record RISCV-TCGRestricted {ex : Execution {arch-RISCV}} (rv : RISCVExecution ex) : Set₁ where
  open Δ.Restrict ex
  open RISCV.Relations rv
  
  field
    consistent : IsRISCVConsistent
    
    ev-bound : events ⊆₁ IsRISCVEventTCG


-- # Helpers

module _ {ex : Execution {arch-RISCV}} {rv : RISCVExecution ex} (ex-res : RISCV-TCGRestricted rv) where

  open Execution ex
  open RISCV-TCGRestricted ex-res


  ¬ev-bound : {ev : EventRISCV}
    → ev ∈ events
    → ¬ (IsRISCVEventTCG ev)
    → ⊥
  ¬ev-bound ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply ev-bound ev∈ex)


  module _ (wf : WellFormed ex) where
  
    open WellFormed wf


    po-bound : po ⊆₂ IsRISCVEventTCG ×₂ IsRISCVEventTCG
    po-bound = ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ po-elements)) (×₂-lift ev-bound ev-bound)

    rf-bound : rf ⊆₂ IsRISCVEventTCG ×₂ IsRISCVEventTCG
    rf-bound = ⊆₂-trans (×₂-lift-udr rf-elements) (×₂-lift ev-bound ev-bound)

    co-bound : co ⊆₂ IsRISCVEventTCG ×₂ IsRISCVEventTCG
    co-bound = ⊆₂-trans (×₂-lift-udr co-elements) (×₂-lift ev-bound ev-bound)

    rmw-bound : rmw ⊆₂ IsRISCVEventTCG ×₂ IsRISCVEventTCG
    rmw-bound = ⊆₂-trans rmw-def (⊆₂-trans imm-⊆₂ po-bound)
