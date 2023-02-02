{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic.Mapping
  {dst : Execution {arch-Armv8}}
  (dst-a8 : Armv8Execution)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst dst-a8)
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
open import Arch.TCG as TCG


open import MapTCGtoArmv8NonAtomic -- defines the stuff we're proving

open import Proof.Mapping.TCGtoArmv8NonAtomic.Execution dst-a8 dst-wf dst-ok as Ex -- defines δ
open Ex.Extra

open Δ.Consistency δ

open Armv8-TCGRestricted


-- Instrs: LD ↦ LDR
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
src-rule-ld : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvR₌ x v (lab-r tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov) a')
src-rule-ld {a} a-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r


-- Instrs: ST ↦ STR
-- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
src-rule-st : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvW₌ x v (lab-w tmov) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov) a')
src-rule-st {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


-- Instrs: RMW ↦ DMBFF;RMW;DMBFF
--
-- Events: Rₗ;rmw;Wₗ           ↦ Aₗ;amo;Lₗ  || successful RMW
-- Events: Rₗ                  ↦ Aₗ         || failed RMW

src-rule-rmw-dom : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvR₌ x v (lab-r trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw) a')
src-rule-rmw-dom {a} {b} a-r a∈src =
  (ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r)


src-rule-rmw-codom : ∀ {a : EventTCG} {x : Location} {v : Value}
  → EvW₌ x v (lab-w trmw) a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w trmw) a')
src-rule-rmw-codom {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


private
  r₌⇒rₜ : {x : EventTCG} {loc : Location} {val : Value}
    → EvR₌ loc val (lab-r trmw) x → EvRₜ trmw x
  r₌⇒rₜ ev-r = ev-r refl

  w₌⇒wₜ : {x : EventTCG} {loc : Location} {val : Value}
    → EvW₌ loc val (lab-w trmw) x → EvWₜ trmw x
  w₌⇒wₜ ev-w = ev-w refl

open Armv8Execution dst-a8

src-rule-rmw-ok : ∀ {a b c d : EventTCG} {x : Location} {v₁ v₂ : Value}
  → EvSkip a
  → EvR₌ x v₁ (lab-r trmw) b
  → EvW₌ x v₂ (lab-w trmw) c
  → EvSkip d
  → po-imm src a b
  → rmw src b c
  → po-imm src c d
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × lxsx b' c' × po-imm dst c' d'
      × EvFₘ F-full a' × EvR₌ x v₁ (lab-r trmw) b' × EvW₌ x v₂ (lab-w trmw) c' × Armv8.EvFₘ F-full d')
src-rule-rmw-ok {a} {b} {c} {d} a-skip b-r c-w d-skip pi[ab] rmw[bc] pi[cd] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src , ev[⇒] d∈src ,
    pi[⇒] a∈src b∈src pi[ab] , rmw[⇒]lxsx b∈src c∈src rmw[bc] , pi[⇒] c∈src d∈src pi[cd] ,
    pre-ff , R₌[⇒] b∈src b-r , W₌[⇒] c∈src c-w , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poˡ∈src (proj₁ pi[cd])
  d∈src = poʳ∈src (proj₁ pi[cd])
  ¬init-c : ¬ EvInit (ev[⇒] c∈src)
  ¬init-c c-init = disjoint-wₜ _ (init⇒wₜ (Init[⇐$] c∈src c-init) , w₌⇒wₜ c-w)
  pre-ff : EvFₘ F-full (ev[⇒] {a} a∈src)
  pre-ff =
    let (w , pi[wb] , w-org) = rmw-ff-l dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r))
        -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
        w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst (org-f-pre-rmw dst-ok) w≡a w-org)
  post-ff : EvFₘ F-full (ev[⇒] {d} d∈src)
  post-ff =
    let (w , pi[cw] , w-org) = rmw-ff-r-ok dst-ok (rmw[⇒] b∈src c∈src rmw[bc])
        -- Somehow, matching `w≡d` to `refl` hangs typechecking forever
        w≡d = po-immʳ dst-wf ¬init-c pi[cw] (pi[⇒] c∈src d∈src pi[cd])
    in org-f-post-rmw-f dst-ok (subst (org-f-post-rmw dst-ok) w≡d w-org)

src-rule-rmw-fail : ∀ {a b c : EventTCG} {x : Location} {v : Value}
  → EvSkip a
  → EvR₌ x v (lab-r trmw) b
  → EvSkip c
  → po-imm src a b
  → b ∉ dom (rmw src)
  → po-imm src b c
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
      × EvFₘ F-full a' × EvR₌ x v (lab-r trmw) b' × EvFₘ F-full c')
src-rule-rmw-fail {a} {b} {c} a-skip b-r c-skip pi[ab] b∉rmwˡ pi[bc] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src ,
    pi[⇒] a∈src b∈src pi[ab] , ¬rmwˡ[⇒] b∈src b∉rmwˡ , pi[⇒] b∈src c∈src pi[bc] ,
    pre-ff , R₌[⇒] b∈src b-r , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poʳ∈src (proj₁ pi[bc])
  ¬init-b : ¬ EvInit (ev[⇒] b∈src)
  ¬init-b b-init = disjoint-r/init _ (rₜ⇒r (r₌⇒rₜ b-r) , Init[⇐$] b∈src b-init)
  pre-ff : EvFₘ F-full (ev[⇒] {a} a∈src)
  pre-ff =
    let (w , pi[wb] , w-org) = rmw-ff-l dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r))
        -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
        w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst (org-f-pre-rmw dst-ok) w≡a w-org)
  post-ff : EvFₘ F-full (ev[⇒] {c} c∈src)
  post-ff =
    let (w , pi[bw] , w-org) = rmw-ff-r-fail dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r)) (¬rmwˡ[⇒] b∈src b∉rmwˡ)
        -- Somehow, matching `w≡c` to `refl` hangs typechecking forever
        w≡c = po-immʳ dst-wf ¬init-b pi[bw] (pi[⇒] b∈src c∈src pi[bc])
    in org-f-post-rmw-f dst-ok (subst (org-f-post-rmw dst-ok) w≡c w-org)


-- Instrs: F_LD_LD F_LD_ST F_LD_M ↦ DMBLD
-- Events: F_RR    F_RW    F_RM   ↦ F_LD

src-rule-f-ld : ∀ {a : EventTCG}
  → {m : TCG.LabF}
  → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
  → EvFₜ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-ld a')
src-rule-f-ld p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ld p a∈src a-f


-- Instrs: F_ST_ST ↦ DMBST
-- Events: F_WW    ↦ F_ST

src-rule-f-st : ∀ {a : EventTCG}
  → EvFₜ WW a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-st a')
src-rule-f-st a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Fww[⇒] a∈src a-f


-- Instrs: F_ST_LD F_ST_M F_M_LD F_M_ST F_M_M F_SC ↦ DMBFF
-- Events: F_WR    F_WM   F_MR   F_MW   F_MM  F_SC ↦ F

src-rule-f-full : ∀ {a : EventTCG}
  → {m : TCG.LabF}
  → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
  → EvFₜ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvFₘ F-full a')
src-rule-f-full p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ff p a∈src a-f


-- Instrs: F_ACQ F_REL ↦ skip
-- Events: F_ACQ F_REL ↦ skip

src-rule-f-skip : ∀ {a : EventTCG}
  → {m : TCG.LabF}
  → m ∈ₗ (ACQ ∷ REL ∷ [])
  → EvFₜ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-f-skip p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]skip p a∈src a-f


mapping : TCG⇒Armv8 src dst dst-a8
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
    ; rule-f-skip    = src-rule-f-skip
    }
