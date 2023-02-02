{-# OPTIONS --safe #-}


module MapTCGtoArmv8Atomic where

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
open import Arch.Armv8 as Armv8


-- Mapping - TCG ⇒ Armv8
--
-- Instruction mapping:
--
-- LD       ↦  LDR
-- ST       ↦  STR
-- RMW      ↦  CAS_AL
--
-- F_LD_LD  ↦  DMBLD
-- F_LD_ST  ↦  DMBLD
-- F_LD_M   ↦  DMBLD
--
-- F_ST_ST  ↦  DMBST
--
-- F_ST_LD  ↦  DMBFF
-- F_ST_M   ↦  DMBFF
-- F_M_LD   ↦  DMBFF
-- F_M_ST   ↦  DMBFF
-- F_M_M    ↦  DMBFF
-- F_SC     ↦  DMBFF
--
--
-- Corresponding event mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  Aₗ;amo;Lₗ  || successful RMW
-- Rₗ         ↦  Aₗ         || failed RMW
--
-- F_RR       ↦  F_LD
-- F_RW       ↦  F_LD
-- F_RM       ↦  F_LD
--
-- F_WW       ↦  F_ST
--
-- F_WR       ↦  F_FULL
-- F_WM       ↦  F_FULL
-- F_MR       ↦  F_FULL
-- F_MW       ↦  F_FULL
-- F_MM       ↦  F_FULL
-- F_SC       ↦  F_FULL


record TCG⇒Armv8
    (src : Execution {arch-TCG})
    (dst : Execution {arch-Armv8})
    (dst-a8 : Armv8Execution) : Set where
    
  open Δ.Defs
  open TCG.LabR
  open TCG.LabW
  open Armv8Execution dst-a8

  field
    -- Instrs: LD ↦ LDR
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
    rule-ld : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r tmov) a')

    -- Instrs: ST ↦ STR
    -- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
    rule-st : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvW₌ x v (lab-w tmov) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w tmov) a')

    -- Instrs: RMW        ↦ CAS_AL
    -- Events: Rₗ;rmw;Wₗ  ↦ Aₗ;amo;Lₗ  || successful RMW
    --         Rₗ         ↦ Aₗ         || failed RMW

    rule-rmw-dom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-a trmw) a')
      
    rule-rmw-codom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvW₌ x v (lab-w trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-l trmw) a')

    rule-rmw-ok : ∀ {a b : EventTCG} {x : Location} {v₁ v₂ : Value}
      → EvR₌ x v₁ (lab-r trmw) a
      → EvW₌ x v₂ (lab-w trmw) b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (amo a' b' × EvR₌ x v₁ (lab-a trmw) a' × EvW₌ x v₂ (lab-l trmw) b')

    rule-rmw-fail : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → a ∉ dom (rmw src)
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-a trmw) a' × a' ∉ dom (rmw dst))

    -- Instrs: F_LD_LD F_LD_ST F_LD_M ↦ DMBLD
    -- Events: F_RR    F_RW    F_RM   ↦ F_LD
      
    rule-f-ld : ∀ {a : EventTCG}
      → {m : TCG.LabF}
      → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
      → EvFₜ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvFₘ F-ld a')
      
    -- Instrs: F_ST_ST ↦ DMBST
    -- Events: F_WW    ↦ F_ST
    
    rule-f-st : ∀ {a : EventTCG}
      → EvFₜ WW a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvFₘ F-st a')

    -- Instrs: F_ST_LD F_ST_M F_M_LD F_M_ST F_M_M F_SC ↦ DMBFF
    -- Events: F_WR    F_WM   F_MR   F_MW   F_MM  F_SC ↦ F
    
    rule-f-full : ∀ {a : EventTCG}
      → {m : TCG.LabF}
      → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
      → EvFₜ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvFₘ F-full a')

    -- Instrs: F_ACQ F_REL ↦ skip
    -- Events: F_ACQ F_REL ↦ skip
      
    rule-f-skip : ∀ {a : EventTCG}
      → {m : TCG.LabF}
      → m ∈ₗ (ACQ ∷ REL ∷ [])
      → EvFₜ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')
      

private
  variable
    uid  : UniqueId
    tid  : ThreadId
    mode : F-mode
    loc  : Location
    val  : Value


-- Armv8 programs mapped from TCG can only contain:
-- Rᵣ Wᵣ Aₗ Lₗ F_LD F_ST F_FULL
data IsArmv8EventTCG : Pred₀ EventArmv8 where
  ev-init : IsArmv8EventTCG (event-init uid loc val)
  ev-skip : IsArmv8EventTCG (event-skip uid tid)
  ev-r    : IsArmv8EventTCG (event-r uid tid loc val (lab-r tmov))
  ev-w    : IsArmv8EventTCG (event-w uid tid loc val (lab-w tmov))
  ev-a    : IsArmv8EventTCG (event-r uid tid loc val (lab-a trmw))
  ev-l    : IsArmv8EventTCG (event-w uid tid loc val (lab-l trmw))
  ev-f    : IsArmv8EventTCG (event-f uid tid (lab-f mode))


record Armv8-TCGRestricted (ex : Execution {arch-Armv8}) (a8 : Armv8Execution) : Set₁ where
  open Δ.Restrict ex
  open Armv8.Relations ex a8
  open Armv8Execution a8
  
  field
    consistent : IsArmv8Consistent
    
    ev-bound : events ⊆₁ IsArmv8EventTCG

    -- Denotes where the events originate in the target. If the mapping were defined on the
    -- /instruction level/, it is obvious where /instructions/ in the target come from.
    -- However, as the instructions are absent in our model, we annotate events accordingly.

    -- Full fences in Armv8 can be produced from WR / WM / MR / MW / MM / SC fences in TCG
    org-f-wr org-f-wm org-f-mr org-f-mw org-f-mm org-f-sc : Pred₀ EventArmv8

    -- Load fences in Armv8 can be produced from RR / RW / RW fences in TCG
    org-ld-rr org-ld-rw org-ld-rm : Pred₀ EventArmv8

    -- Skip events in Armv8 can be produced from either:
    -- * skips in TCG
    -- * ACQ / REL fences in TCG
    org-skip-skip org-skip-acq org-skip-rel : Pred₀ EventArmv8
    
    -- Store fences can only be created from `WW` fences. No need to keep track


    unique-org-f-wr : UniquePred org-f-wr
    unique-org-f-wm : UniquePred org-f-wm
    unique-org-f-mr : UniquePred org-f-mr
    unique-org-f-mw : UniquePred org-f-mw
    unique-org-f-mm : UniquePred org-f-mm
    unique-org-f-sc : UniquePred org-f-sc

    unique-org-ld-rr : UniquePred org-ld-rr
    unique-org-ld-rw : UniquePred org-ld-rw
    unique-org-ld-rm : UniquePred org-ld-rm

    unique-org-skip-skip : UniquePred org-skip-skip
    unique-org-skip-acq  : UniquePred org-skip-acq
    unique-org-skip-rel  : UniquePred org-skip-rel

    org-f-def    : (events ∩₁ EvFₘ F-full) ⇔₁ (org-f-wr ∪₁ org-f-wm ∪₁ org-f-mr ∪₁ org-f-mw ∪₁ org-f-mm ∪₁ org-f-sc)
    org-ld-def   : (events ∩₁ EvFₘ F-ld) ⇔₁ (org-ld-rr ∪₁ org-ld-rw ∪₁ org-ld-rm)
    org-skip-def : (events ∩₁ EvSkip) ⇔₁ (org-skip-skip ∪₁ org-skip-acq ∪₁ org-skip-rel)

    -- All `rmw` relations are over `amo` by the /atomic/ mapping
    no-lxsx : Empty₂ lxsx

    disjoint-f    : PairwiseDisjoint₁ (org-f-wr ∷ org-f-wm ∷ org-f-mr ∷ org-f-mw ∷ org-f-mm ∷ org-f-sc ∷ [])
    disjoint-ld   : PairwiseDisjoint₁ (org-ld-rr ∷ org-ld-rw ∷ org-ld-rm ∷ [])
    disjoint-skip : PairwiseDisjoint₁ (org-skip-skip ∷ org-skip-acq ∷ org-skip-rel ∷ [])


-- # Helpers

module _ {ex : Execution {arch-Armv8}} {a8 : Armv8Execution} (ex-res : Armv8-TCGRestricted ex a8) where

  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Empty using (⊥-elim)
  open import Function using (_∘_)

  open Execution ex
  open Armv8Execution a8
  open Armv8-TCGRestricted ex-res
  
  ¬ev-bound : {ev : EventArmv8}
    → ev ∈ events
    → ¬ (IsArmv8EventTCG ev)
    → ⊥
  ¬ev-bound ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply ev-bound ev∈ex)

  -- | All atomic reads have acquire ordering semantics (by our mapping)
  Rₐ⇒A : {x : EventArmv8} → x ∈ events → EvRₐ x → EvA x
  Rₐ⇒A {event-r _ _ _ _ (lab-r .trmw)} x∈dst (ev-r refl) = ⊥-elim (¬ev-bound x∈dst (λ()))
  Rₐ⇒A {event-r _ _ _ _ (lab-a .trmw)} _     (ev-r refl) = ev-a

  -- | All atomic writes have release ordering semantics (by our mapping)
  Wₐ⇒L : {x : EventArmv8} → x ∈ events → EvWₐ x → EvL x
  Wₐ⇒L {event-w _ _ _ _ (lab-w .trmw)} x∈dst (ev-w refl) = ⊥-elim (¬ev-bound x∈dst (λ()))
  Wₐ⇒L {event-w _ _ _ _ (lab-l .trmw)} _     (ev-w refl) = ev-l


  module _ (wf : WellFormed ex) where
  
    open WellFormed wf
    open Armv8.Relations.IsArmv8Consistent consistent


    po-bound : po ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    po-bound = ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ po-elements)) (×₂-lift ev-bound ev-bound)

    rf-bound : rf ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    rf-bound = ⊆₂-trans (×₂-lift-udr rf-elements) (×₂-lift ev-bound ev-bound)

    co-bound : co ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    co-bound = ⊆₂-trans (×₂-lift-udr co-elements) (×₂-lift ev-bound ev-bound)

    rmw-bound : rmw ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    rmw-bound = ⊆₂-trans rmw-def (⊆₂-trans imm-⊆₂ po-bound)

    rmw⇒amo : {x y : EventArmv8} → rmw x y → amo x y
    rmw⇒amo = [ id , ⊥-elim ∘ no-lxsx _ _ ] ∘ ⇔₂-apply-⊆₂ amo-lxsx-def
    
