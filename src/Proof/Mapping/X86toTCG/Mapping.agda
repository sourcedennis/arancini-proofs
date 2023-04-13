{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import Arch.Mixed using (MixedExecution)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Mapping
  {dst : Execution {arch-TCG}}
  {dst-tex : MixedExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst-tex)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
-- open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.X86 as X86
open import Arch.TCG


open import MapX86toTCG -- defines the stuff we're proving

open import Proof.Mapping.X86toTCG.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra

open Δ.Consistency δ

open TCG-X86Restricted


private
  W₌⇒Wₜ : {loc : Location} {val : Value} {tag : Tag} {ev : EventX86}
    → EvW₌ loc val (lab-w tag) ev
    → EvWₜ tag ev
  W₌⇒Wₜ ev-w = ev-w refl

  R₌⇒Rₜ : {loc : Location} {val : Value} {tag : Tag} {ev : EventX86}
    → EvR₌ loc val (lab-r tag) ev
    → EvRₜ tag ev
  R₌⇒Rₜ ev-r = ev-r refl
  
  W₌⇒W : {loc : Location} {val : Value} {lab : X86.LabW} {ev : EventX86}
    → EvW₌ loc val lab ev
    → EvW ev
  W₌⇒W ev-w = ev-w

  R₌⇒R : {loc : Location} {val : Value} {lab : X86.LabR} {ev : EventX86}
    → EvR₌ loc val lab ev
    → EvR ev
  R₌⇒R ev-r = ev-r


-- Instrs: RMOV    ↦ LD;F_LD_M
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
src-rule-rmov : ∀ {a b : EventX86} {x : Location} {v : Value}
  → EvR₌ x v (lab-r tmov) a
  → EvSkip b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × EvR₌ x v (lab-r tmov) a' × EvFₜ RM b')
src-rule-rmov {a} {b} a-r₌ b-skip pi[ab] =
  let a∈src = poˡ∈src (proj₁ pi[ab])
      (z , pi[az] , z-is-f) = r-f-po₁ dst-ok (events[⇒] {a} a∈src) (Rₜ[⇒] a∈src (R₌⇒Rₜ a-r₌))
      -- Note: z≡b : z ≡ ev[⇒] b∈src
  in _ , _ , pi[az] , R₌[⇒] a∈src a-r₌ , z-is-f


-- Instrs: WMOV   ↦ F_ST_ST;ST
-- Events: W(x,v) ↦ F_WW;W(x,v)
src-rule-wmov : ∀ {a b : EventX86}
    {x : Location} {v : Value}
  → EvSkip a
  → EvW₌ x v (lab-w tmov) b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × EvFₜ WW a' × EvW₌ x v (lab-w tmov) b')
src-rule-wmov {a} {b} a-skip b-w pi[ab] =
  let a∈src = poˡ∈src (proj₁ pi[ab])
      b∈src = poʳ∈src (proj₁ pi[ab])
      (z , pi[zb] , z-is-f) = f-w-po₁ dst-ok {ev[⇒] {a} a∈src} (events[⇒] {b} b∈src) (Wₜ[⇒] b∈src (W₌⇒Wₜ b-w))
      z≡a : z ≡ ev[⇒] a∈src
      z≡a = po-immˡ dst-wf pi[zb] (pi[⇒] {a} {b} a∈src b∈src pi[ab])
  in ev[⇒] a∈src , ev[⇒] b∈src , pi[⇒] {a} {b} a∈src b∈src pi[ab] , subst (EvFₜ WW) z≡a z-is-f , W₌[⇒] b∈src b-w


-- Instrs: RMW ↦ RMW
-- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
--         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
src-rule-rmw-ok : ∀ {a b : EventX86}
    {x : Location} {v₁ v₂ : Value}
  → EvR₌ x v₁ (lab-r trmw) a
  → EvW₌ x v₂ (lab-w trmw) b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × EvR₌ x v₁ (lab-r trmw) a' × EvW₌ x v₂ (lab-w trmw) b')
src-rule-rmw-ok {a} {b} a-r b-w rmw[ab] =
  let a∈src = rmwˡ∈src rmw[ab]
      b∈src = rmwʳ∈src rmw[ab]
  in ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src a-r , W₌[⇒] b∈src b-w


src-rule-rmw-fail : ∀ {a : EventX86}
    {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw) a')
src-rule-rmw-fail {a} a-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r


-- Instrs: MFENCE ↦ F_MM
-- Events: F      ↦ F_MM
src-rule-fence : ∀ {a : EventX86}
  → EvF a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₜ MM a')
src-rule-fence {a} a-f a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , F[⇒] a∈src a-f


mapping : X86⇒TCG src dst
mapping =
  record
    { rule-rmov     = src-rule-rmov
    ; rule-wmov     = src-rule-wmov
    ; rule-rmw-ok   = src-rule-rmw-ok
    ; rule-rmw-fail = src-rule-rmw-fail
    ; rule-fence    = src-rule-fence
    }
