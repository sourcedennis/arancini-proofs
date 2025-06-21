{-# OPTIONS --safe #-}

module MapX86toAIMM where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Unary using (Pred; _∈_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.X86 as X86 using (EventX86; arch-x86)
open import Arch.AIMM as AIMM
open import Arch.Mixed using (MixedExecution)

open import Burrow.Template.Mapping as Δ


-- # Definitions

-- Mapping - X86 ⇒ AIMM
--
--
-- Instruction mapping:
--
-- RMOV   ↦ LD;F_LD_M
-- WMOV   ↦ F_ST_ST;ST
-- RMW    ↦ RMW
-- MFENCE ↦ F_MM
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)             ↦ Rᵣ(x,v);F_RM
-- W(x,v)              ↦ F_WW;Wᵣ(x,v)
-- Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;Wₗ(x,v')  || successful RMW
-- Rₗ(x,v)             ↦ Rₗ(x,v)               || failed RMW
-- F                   ↦ F_MM

record X86⇒AIMM (src : Execution {arch-x86}) (dst : Execution {arch-AIMM}) : Set where
  open Δ.Defs
  open X86.LabR
  open X86.LabW
  
  field
    -- Instrs: RMOV    ↦ LD;F_LD_M
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    rule-rmov : ∀ {a b : EventX86} {x : Location} {v : Value}
      → EvR₌ x v (lab-r tmov) a
      → EvSkip b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × EvR₌ x v (lab-r tmov) a' × EvFₜ RM b')

    -- Instrs: WMOV   ↦ F_ST_ST;ST
    -- Events: W(x,v) ↦ F_WW;W(x,v)
    rule-wmov : ∀ {a b : EventX86} {x : Location} {v : Value}
      → EvSkip a
      → EvW₌ x v (lab-w tmov) b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × EvFₜ WW a' × EvW₌ x v (lab-w tmov) b')

    -- Instrs: RMW ↦ RMW
    -- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
    --         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
    rule-rmw-ok : ∀ {a b : EventX86} {x : Location} {v₁ v₂ : Value}
      → EvR₌ x v₁ (lab-r trmw) a
      → EvW₌ x v₂ (lab-w trmw) b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × EvR₌ x v₁ (lab-r trmw) a' × EvW₌ x v₂ (lab-w trmw) b')
      
    rule-rmw-fail : ∀ {a : EventX86}
        {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw) a')

    -- Instrs: MFENCE ↦ F_SC
    -- Events: F      ↦ F_SC
    rule-fence : ∀ {a : EventX86}
      → EvF a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvFₜ AIMM.MM a')


private
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    tag : Tag


-- AIMM programs mapped from x86 programs can only contain these events.
-- Rᵣ Rₗ Wᵣ Wₗ F_RM F_WW F_MM
data IsAIMMEventX86 : Pred₀ EventAIMM where
  ev-init : IsAIMMEventX86 (event-init uid loc val)
  ev-r    : IsAIMMEventX86 (event-r uid tid loc val (lab-r tag))
  ev-w    : IsAIMMEventX86 (event-w uid tid loc val (lab-w tag))
  ev-frm  : IsAIMMEventX86 (event-f uid tid RM)
  ev-fww  : IsAIMMEventX86 (event-f uid tid WW)
  ev-fmm  : IsAIMMEventX86 (event-f uid tid MM)


-- | A proof that a AIMM execution could only have been generated from a AIMM program
-- that is mapped from an X86 program.
--
-- This follows from mappings on the instruction-level. (Which we omit)
record AIMM-X86Restricted {ex : Execution {arch-AIMM}} (tex : MixedExecution ex) : Set₁ where
  open Δ.Restrict ex
  open AIMM.Relations tex
    
  field
    consistent : IsAIMMConsistent
    
    ev-bound : events ⊆₁ IsAIMMEventX86
    
    -- Read events that are generated from the LD instruction are /always/ followed by a F_RM fence.
    -- By the rule: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    -- There is no other way of obtaining a Rᵣ event.
    r-f-po₁ : ∀ {a : EventAIMM} → a ∈ events → EvRₜ tmov a → ∃[ b ] (po-imm a b × EvFₜ RM b)
    r-f-po₂ : ∀ {b : EventAIMM} → b ∈ events → EvFₜ RM b → ∃[ a ] (po-imm a b × EvRₜ tmov a)

    -- Rule: W(x,v) ↦ F_WW;W(x,v)
    -- Every non-rmw write (ST) is preceded by a F_WW event
    f-w-po₁ : ∀ {a b : EventAIMM} → b ∈ events → EvWₜ tmov b → ∃[ a ] (po-imm a b × EvFₜ WW a)
    -- Every F_WW event is followed by a W event
    f-w-po₂ : ∀ {a b : EventAIMM} → a ∈ events → EvFₜ WW a → ∃[ b ] (po-imm a b × EvWₜ tmov b)


-- # Helpers

module _ {ex : Execution {arch-AIMM}} {tex : MixedExecution ex} (ex-res : AIMM-X86Restricted tex) where

  open Δ.Restrict ex
  open AIMM-X86Restricted ex-res


  ¬ev-bound :
      {ev : EventAIMM}
    → ev ∈ events
    → ¬ (IsAIMMEventX86 ev)
    → ⊥
  ¬ev-bound ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply ev-bound ev∈ex)


  module _ (wf : WellFormed ex) where

    open WellFormed wf


    po-bound : po ⊆₂ IsAIMMEventX86 ×₂ IsAIMMEventX86
    po-bound =
      ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ po-elements)) (×₂-lift ev-bound ev-bound)

    rf-bound : rf ⊆₂ IsAIMMEventX86 ×₂ IsAIMMEventX86
    rf-bound =
      ⊆₂-trans (×₂-lift-udr rf-elements) (×₂-lift ev-bound ev-bound)

    co-bound : co ⊆₂ IsAIMMEventX86 ×₂ IsAIMMEventX86
    co-bound = ⊆₂-trans (×₂-lift-udr co-elements) (×₂-lift ev-bound ev-bound)

    rmw-bound : rmw ⊆₂ IsAIMMEventX86 ×₂ IsAIMMEventX86
    rmw-bound = ⊆₂-trans rmw-def (⊆₂-trans imm-⊆₂ po-bound)
