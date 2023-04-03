{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.RISCV using (arch-RISCV; RISCVExecution)
open import MapTCGtoRISCV using (RISCV-TCGRestricted)


module Proof.Mapping.TCGtoRISCV.Mapping
  {dst : Execution {arch-RISCV}}
  {dst-rv : RISCVExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : RISCV-TCGRestricted dst-rv)
  where
  
-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_; _∉_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Data.List using (_∷_; [])
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
-- Library imports
open import Dodo.Binary hiding (REL)
-- Local imports
open import Helpers
open import Arch.RISCV as RISCV
open import Arch.TCG as TCG


open import MapTCGtoRISCV -- defines the stuff we're proving

open import Proof.Mapping.TCGtoRISCV.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra

open Δ.Consistency δ



-- Instrs: LD ↦ LD
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
src-rule-ld : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvR₌ x v (lab-r tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov ann-none) a')
src-rule-ld {a} a-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r


-- Instrs: ST ↦ STR
-- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
src-rule-st : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvW₌ x v (lab-w tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov ann-none) a')
src-rule-st {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


-- Instrs: RMW        ↦  RMW_SC
-- Events: Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ  || successful RMW
--         Rₐ         ↦  Rₐ         || failed RMW

src-rule-rmw-dom : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw ann-acqrel) a')
src-rule-rmw-dom {a} a-r a∈src =
  (ev[⇒] {a} a∈src , events[⇒] {a} a∈src , R₌[⇒]sc a∈src a-r)


src-rule-rmw-codom : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvW₌ x v (lab-w trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w trmw ann-acqrel) a')
src-rule-rmw-codom {a} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] {a} a∈src , W₌[⇒]sc a∈src a-w


src-rule-rmw-ok : ∀ {a b : EventTCG} {x : Location} {v₁ v₂ : Value}
  → EvR₌ x v₁ (lab-r trmw) a
  → EvW₌ x v₂ (lab-w trmw) b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × EvR₌ x v₁ (lab-r trmw ann-acqrel) a' × EvW₌ x v₂ (lab-w trmw ann-acqrel) b')
src-rule-rmw-ok {a} {b} a-r b-w rmw[ab] =
  ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒]sc a∈src a-r , W₌[⇒]sc b∈src b-w
  where
  a∈src = rmwˡ∈src rmw[ab]
  b∈src = rmwʳ∈src rmw[ab]


src-rule-rmw-fail : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → a ∉ dom (rmw src)
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw ann-acqrel) a' × a' ∉ dom (rmw dst))
src-rule-rmw-fail {a} a-rₐ a∈src a∉rmwˡ =
  ev[⇒] a∈src , events[⇒] a∈src , R₌[⇒]sc a∈src a-rₐ , ¬rmwˡ[⇒] a∈src a∉rmwˡ


-- Basically, the fences remain the same.

src-rule-f : ∀ {a : EventTCG} {f : TCG.LabF}
  → EvFₜ f a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₜ (rule-labf f) a')
src-rule-f x-f a∈src = ev[⇒] a∈src , events[⇒] a∈src , Fₜ[⇒] a∈src x-f


mapping : TCG⇒RISCV src dst-rv
mapping =
  record
    { rule-ld        = src-rule-ld
    ; rule-st        = src-rule-st
    ; rule-rmw-dom   = src-rule-rmw-dom
    ; rule-rmw-codom = src-rule-rmw-codom
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-rmw-fail  = src-rule-rmw-fail
    ; rule-f         = src-rule-f
    }
