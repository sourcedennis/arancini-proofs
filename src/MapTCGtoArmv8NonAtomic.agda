{-# OPTIONS --safe #-}


module MapTCGtoArmv8NonAtomic where

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


-- # Definitions

-- Mapping - TCG ⇒ ARMv8
--
-- Instruction mapping:
--
-- LD       ↦  LDR
-- ST       ↦  STR
-- RMW      ↦  DMBFF;RMW;DMBFF
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
-- Rₗ;rmw;Wₗ  ↦  F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
-- Rₗ         ↦  F_FULL;Rₗ;F_FULL          || failed RMW
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

    -- Instrs: RMW ↦ DMBFF;RMW;DMBFF
    -- Events: Rₗ;rmw;Wₗ  ↦ F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
    --         Rₗ         ↦ F_FULL;Rₗ;F_FULL          || failed RMW

    rule-rmw-dom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvR₌ x v (lab-r trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvR₌ x v (lab-r trmw) a')
      
    rule-rmw-codom : ∀ {a : EventTCG} {x : Location} {v : Value}
      → EvW₌ x v (lab-w trmw) a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvW₌ x v (lab-w trmw) a')

    rule-rmw-ok : ∀ {a b c d : EventTCG} {x : Location} {v₁ v₂ : Value}
      → EvSkip a
      → EvR₌ x v₁ (lab-r trmw) b
      → EvW₌ x v₂ (lab-w trmw) c
      → EvSkip d
      → po-imm src a b
      → rmw src b c
      → po-imm src c d
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × lxsx b' c' × po-imm dst c' d'
          × EvFₘ F-full a' × EvR₌ x v₁ (lab-r trmw) b' × EvW₌ x v₂ (lab-w trmw) c' × EvFₘ F-full d')

    rule-rmw-fail : ∀ {a b c : EventTCG} {x : Location} {v : Value}
      → EvSkip a
      → EvR₌ x v (lab-r trmw) b
      → EvSkip c
      → po-imm src a b
      → b ∉ dom (rmw src)
      → po-imm src b c
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
          × EvFₘ F-full a' × EvR₌ x v (lab-r trmw) b' × EvFₘ F-full c')

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
    
    rule-f-full : ∀ {a b : EventTCG}
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
    tag  : Tag
    mode : F-mode
    loc  : Location
    val  : Value

-- Armv8 programs mapped from TCG can only contain:
-- R W F_LD F_ST F_FULL
data IsArmv8EventTCG : Pred₀ EventArmv8 where
  ev-init : IsArmv8EventTCG (event-init uid loc val)
  ev-skip : IsArmv8EventTCG (event-skip uid tid)
  ev-r    : IsArmv8EventTCG (event-r uid tid loc val (lab-r tag))
  ev-w    : IsArmv8EventTCG (event-w uid tid loc val (lab-w tag))
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


    -- # Design Decision: Predicates
    --
    -- We could alternative define:
    --
    -- > org-f : EventArmv8 → OrgF
    --
    -- That seemingly simplifies our definitions. However, it does not enforce `OrgF` only
    -- existing for full fences in our execution. Doing so results in:
    --
    -- > org-f : (x : EventArmv8) → x ∈ events → EvF₌ F-full x → OrgF
    --
    -- The problem with this definition is that the caller is responsible for proving
    -- that `x ∈ events` and `EvF₌ F-full x`. In our axioms (below), that becomes tricky.
    -- Consider `rmw-ff-l`, which then becomes:
    --
    -- > rmw-ff-l : {b : EventArmv8}
    -- >   → b ∈ events
    -- >   → EvRₜ trmw b
    -- >   → ∃[ a ] ∃[ pi[ab] ] ∃[ a-f ] (org-f a (piˡ∈ex wf pi[ab]) a-f ≡ org-f-wr)
    --
    -- That becomes clumsy to use. Particularly:
    -- * When using it, we (often) have to substitute `piˡ∈ex wf pi[ab]`
    -- * We have to deal with the equality (_≡_)
    --
    -- To avoid that, we make the definitions here slightly more verbose - with predicates
    -- and axioms over them - which makes the proof effort easier later on.


    -- Full fences in Armv8 can be produced from either:
    -- * WR / WM / MR / MW / MM / SC fences in TCG
    -- * Around a RMW operation - corresponding to skip events in the source
    org-f-wr org-f-wm org-f-mr org-f-mw org-f-mm org-f-sc
      org-f-pre-rmw org-f-post-rmw : Pred₀ EventArmv8

    -- Load fences in Armv8 can be produced from RR / RW / RW fences in TCG
    org-ld-rr org-ld-rw org-ld-rm : Pred₀ EventArmv8

    -- Skip events in Armv8 can be produced from either:
    -- * skips in TCG
    -- * ACQ / REL fences in TCG
    org-skip-skip org-skip-acq org-skip-rel : Pred₀ EventArmv8
    
    -- Store fences can only be created from `WW` fences. No need to keep track


    unique-org-f-wr       : UniquePred org-f-wr
    unique-org-f-wm       : UniquePred org-f-wm
    unique-org-f-mr       : UniquePred org-f-mr
    unique-org-f-mw       : UniquePred org-f-mw
    unique-org-f-mm       : UniquePred org-f-mm
    unique-org-f-sc       : UniquePred org-f-sc
    unique-org-f-pre-rmw  : UniquePred org-f-pre-rmw
    unique-org-f-post-rmw : UniquePred org-f-post-rmw

    unique-org-ld-rr : UniquePred org-ld-rr
    unique-org-ld-rw : UniquePred org-ld-rw
    unique-org-ld-rm : UniquePred org-ld-rm

    unique-org-skip-skip : UniquePred org-skip-skip
    unique-org-skip-acq  : UniquePred org-skip-acq
    unique-org-skip-rel  : UniquePred org-skip-rel

    -- Before every RMW-read there is a full fence
    rmw-ff-l : ∀ {b : EventArmv8} → b ∈ events → EvRₜ trmw b → ∃[ a ] (po-imm a b × org-f-pre-rmw a)
    -- After every successful-RMW-write there is a full fence
    rmw-ff-r-ok : ∀ {a b : EventArmv8} → rmw a b → ∃[ c ] (po-imm b c × org-f-post-rmw c)
    -- After every failed-RMW-read there is a full fence
    rmw-ff-r-fail : ∀ {a : EventArmv8} → a ∈ events → EvRₜ trmw a → a ∉ dom rmw → ∃[ b ] (po-imm a b × org-f-post-rmw b)

    org-f-def    : (events ∩₁ EvFₘ F-full) ⇔₁ (org-f-wr ∪₁ org-f-wm ∪₁ org-f-mr ∪₁ org-f-mw ∪₁ org-f-mm ∪₁ org-f-sc ∪₁ org-f-pre-rmw ∪₁ org-f-post-rmw)
    org-ld-def   : (events ∩₁ EvFₘ F-ld) ⇔₁ (org-ld-rr ∪₁ org-ld-rw ∪₁ org-ld-rm)
    org-skip-def : (events ∩₁ EvSkip) ⇔₁ (org-skip-skip ∪₁ org-skip-acq ∪₁ org-skip-rel)

    -- All `rmw` relations are over `lxsx` by the /non-atomic/ mapping
    no-amo : Empty₂ amo

    disjoint-f    : PairwiseDisjoint₁ (org-f-wr ∷ org-f-wm ∷ org-f-mr ∷ org-f-mw ∷ org-f-mm ∷ org-f-sc ∷ org-f-pre-rmw ∷ org-f-post-rmw ∷ [])
    disjoint-ld   : PairwiseDisjoint₁ (org-ld-rr ∷ org-ld-rw ∷ org-ld-rm ∷ [])
    disjoint-skip : PairwiseDisjoint₁ (org-skip-skip ∷ org-skip-acq ∷ org-skip-rel ∷ [])


-- # Helpers

module _ {ex : Execution {arch-Armv8}} {a8 : Armv8Execution} (ex-res : Armv8-TCGRestricted ex a8) where

  open import Helpers
  open import Data.Product using (proj₂)
  open import Data.Empty using (⊥-elim)
  open import Function using (_∘_)

  open Δ.Restrict ex
  open Armv8-TCGRestricted ex-res


  ¬ev-bound :
      {ev : EventArmv8}
    → ev ∈ events
    → ¬ (IsArmv8EventTCG ev)
    → ⊥
  ¬ev-bound ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply ev-bound ev∈ex)

  org-f-pre-rmw-f :
      {x : EventArmv8}
    → org-f-pre-rmw x
    → EvFₘ F-full x
  org-f-pre-rmw-f = proj₂ ∘ ⇔₁-apply-⊇₁ org-f-def ∘ opt₇

  org-f-post-rmw-f :
      {x : EventArmv8}
    → org-f-post-rmw x
    → EvFₘ F-full x
  org-f-post-rmw-f = proj₂ ∘ ⇔₁-apply-⊇₁ org-f-def ∘ opf₈


  module _ (wf : WellFormed ex) where

    open WellFormed wf
    open Armv8Execution a8
    open Armv8.Relations.IsArmv8Consistent consistent


    po-bound : po ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    po-bound = ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ po-elements)) (×₂-lift ev-bound ev-bound)

    rf-bound : rf ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    rf-bound = ⊆₂-trans (×₂-lift-udr rf-elements) (×₂-lift ev-bound ev-bound)

    co-bound : co ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    co-bound = ⊆₂-trans (×₂-lift-udr co-elements) (×₂-lift ev-bound ev-bound)

    rmw-bound : rmw ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
    rmw-bound = ⊆₂-trans rmw-def (⊆₂-trans imm-⊆₂ po-bound)

    rmw⇒lxsx : {x y : EventArmv8} → rmw x y → lxsx x y
    rmw⇒lxsx = [ ⊥-elim ∘ no-amo _ _ , id ] ∘ ⇔₂-apply-⊆₂ amo-lxsx-def
