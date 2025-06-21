{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapAIMMtoArmv8 using (Armv8-AIMMRestricted)


module Proof.Mapping.AIMMtoArmv8.Mapping
  {dst : Execution {arch-Armv8}}
  {dst-a8 : Armv8Execution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-AIMMRestricted dst-a8)
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
open import Arch.Armv8 as Armv8
open import Arch.AIMM as AIMM


open import MapAIMMtoArmv8 -- defines the stuff we're proving

open import Proof.Mapping.AIMMtoArmv8.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra

open Δ.Consistency δ

open Armv8-AIMMRestricted


-- Instrs: LD ↦ LDR
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
src-rule-ld : ∀ {a : EventAIMM} {x : Location} {v : Value}
  → EvR₌ x v (lab-r tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov) a')
src-rule-ld {a} a-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r


-- Instrs: ST ↦ STR
-- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
src-rule-st : ∀ {a : EventAIMM} {x : Location} {v : Value}
  → EvW₌ x v (lab-w tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov) a')
src-rule-st {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


-- Rₗ;rmw;Wₗ           ↦ Aₗ;amo;Lₗ  || successful RMW
-- Rₗ                  ↦ Aₗ         || failed RMW

src-rule-rmw-dom : ∀ {a : EventAIMM} {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-a trmw) a')
src-rule-rmw-dom {a} a-r a∈src =
  (ev[⇒] {a} a∈src , events[⇒] {a} a∈src , R₌[⇒]A a∈src a-r)

src-rule-rmw-codom : ∀ {a : EventAIMM} {x : Location} {v : Value}
  → EvW₌ x v (lab-w trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-l trmw) a')
src-rule-rmw-codom {a} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] {a} a∈src , W₌[⇒]L a∈src a-w

open Armv8Execution dst-a8

src-rule-rmw-ok : ∀ {a b : EventAIMM} {x : Location} {v₁ v₂ : Value}
  → EvR₌ x v₁ (lab-r trmw) a
  → EvW₌ x v₂ (lab-w trmw) b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (amo a' b' × EvR₌ x v₁ (lab-a trmw) a' × EvW₌ x v₂ (lab-l trmw) b')
src-rule-rmw-ok {a} {b} a-r b-w rmw[ab] =
  ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒]amo a∈src b∈src rmw[ab] , R₌[⇒]A a∈src a-r , W₌[⇒]L b∈src b-w
  where
  a∈src = rmwˡ∈src rmw[ab]
  b∈src = rmwʳ∈src rmw[ab]


src-rule-rmw-fail : ∀ {a : EventAIMM} {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → a ∉ dom (rmw src)
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-a trmw) a' × a' ∉ dom (rmw dst))
src-rule-rmw-fail {a} a-rₐ a∈src a∉rmwˡ =
  ev[⇒] a∈src , events[⇒] a∈src , R₌[⇒]A a∈src a-rₐ , ¬rmwˡ[⇒] a∈src a∉rmwˡ


-- Instrs: F_LD_LD F_LD_ST F_LD_M ↦ DMBLD
-- Events: F_RR    F_RW    F_RM   ↦ F_LD

src-rule-f-ld : ∀ {a : EventAIMM}
  → {m : AIMM.LabF}
  → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
  → EvFₜ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-ld a')
src-rule-f-ld p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ld p a∈src a-f


-- Instrs: F_ST_ST ↦ DMBST
-- Events: F_WW    ↦ F_ST

src-rule-f-st : ∀ {a : EventAIMM}
  → EvFₜ WW a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-st a')
src-rule-f-st a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Fww[⇒] a∈src a-f


-- Instrs: F_ST_LD F_ST_M F_M_LD F_M_ST F_M_M F_SC ↦ DMBFF
-- Events: F_WR    F_WM   F_MR   F_MW   F_MM  F_SC ↦ F

src-rule-f-full : ∀ {a : EventAIMM}
  → {m : AIMM.LabF}
  → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ [])
  → EvFₜ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-full a')
src-rule-f-full p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ff p a∈src a-f


mapping : AIMM⇒Armv8 src dst-a8
mapping =
  record
    { rule-ld        = src-rule-ld
    ; rule-st        = src-rule-st
    ; rule-rmw-dom   = src-rule-rmw-dom
    ; rule-rmw-codom = src-rule-rmw-codom
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-rmw-fail  = src-rule-rmw-fail
    ; rule-f-ld      = src-rule-f-ld
    ; rule-f-st      = src-rule-f-st
    ; rule-f-full    = src-rule-f-full
    }
