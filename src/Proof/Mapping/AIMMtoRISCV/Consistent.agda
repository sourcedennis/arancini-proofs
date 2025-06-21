{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.RISCV using (arch-RISCV; RISCVExecution)
open import MapAIMMtoRISCV using (RISCV-AIMMRestricted)


module Proof.Mapping.AIMMtoRISCV.Consistent
  {dst : Execution {arch-RISCV}}
  {dst-rv : RISCVExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : RISCV-AIMMRestricted dst-rv)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁) renaming ([_,_] to ⊎[_,_])
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Irreflexive; Transitive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _∷ʳ_; _++_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import MapAIMMtoRISCV
open import Arch.RISCV as RISCV
open import Arch.AIMM as AIMM
open import Helpers

open import Proof.Mapping.AIMMtoRISCV.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra

open Δ.Consistency δ

open AIMM.Relations
open AIMM.Properties

open RISCV.Relations dst-rv

dst-consistent = RISCV-AIMMRestricted.consistent dst-ok

open IsRISCVConsistent dst-consistent


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


src-ax-coherence : Acyclic _≡_ ( Coh src-tex )
src-ax-coherence refl coh⁺[xx] =
  let x∈src = ⁺-lift-predˡ (cohˡ∈ex src-tex src-wf) coh⁺[xx]
      coh⁺[xx]ᵗ = ⁺[⇒]ˡ (cohˡ∈ex src-tex src-wf) coh[⇒] x∈src x∈src coh⁺[xx]
  in ax-coherence refl coh⁺[xx]ᵗ
  where
  coh[⇒] : Rel[⇒] (Coh src-tex) (co dst ∪₂ rf dst ∪₂ fr dst ∪₂ po-loc dst)
  coh[⇒] x∈src y∈src (coh-po-loc pl[xy]) = opf₄ (po-loc[⇒] x∈src y∈src pl[xy])
  coh[⇒] x∈src y∈src (coh-rf rf[xy])     = opt₂ (rf[⇒] x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (coh-fr fr[xy])     = opt₃ (fr[⇒] x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (coh-co co[xy])     = opt₁ (co[⇒] x∈src y∈src co[xy])


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

-- ## Proof

open import Data.Bool using (Bool; true; false)

-- | All atomic R/W events (i.e., produced by RMWs) are produced by instructions
-- with ACQ flags.
rwₐ-acq : {x : EventRISCV} → x ∈ events dst → EvRWₜ trmw x → EvAcq x
rwₐ-acq {event-r _ _ _ _ (lab-r _ (true ⦂ann⦂ _))}  x∈dst (ev-r refl) = ev-acq-r
rwₐ-acq {event-w _ _ _ _ (lab-w _ (true ⦂ann⦂ _))}  x∈dst (ev-w refl) = ev-acq-w
-- impossible cases
rwₐ-acq {event-r _ _ _ _ (lab-r _ (false ⦂ann⦂ _))} x∈dst (ev-r refl) =
  ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
rwₐ-acq {event-w _ _ _ _ (lab-w _ (false ⦂ann⦂ _))} x∈dst (ev-w refl) =
  ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

-- | All atomic Write events (i.e., produced by RMWs) are produced by instructions
-- with REL flags.
wₐ-rel : {x : EventRISCV} → x ∈ events dst → EvWₐ x → EvRel x
wₐ-rel {event-w _ _ _ _ (lab-w .trmw (_ ⦂ann⦂ true))}  x∈dst (ev-w refl) = ev-rel-w
wₐ-rel {event-w _ _ _ _ (lab-w .trmw (_ ⦂ann⦂ false))} x∈dst (ev-w refl) =
  ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

-- | Events in the co-domain of `rmw` are produced by an instruction (i.e., RMW)
-- with ACQ flag.
rmwʳ-acq : {x : EventRISCV} → x ∈ codom (rmw dst) → EvAcq x
rmwʳ-acq (_ , rmw[xy]) =
  let y-wₐ = rmwʳ-w dst-wf (_ , rmw[xy])
      y∈dst = rmwʳ∈ex dst-wf rmw[xy]
  in rwₐ-acq y∈dst (wₜ⇒rwₜ y-wₐ)

src-ax-global-ord : Irreflexive _≡_ (ghb src-tex)
src-ax-global-ord refl ghb[xx] =
  let x∈src = ⁺-lift-predˡ (ghbiˡ∈ex src-tex src-wf) ghb[xx]
      model⁺[xx] = ⁺[⇒]ˡ (ghbiˡ∈ex src-tex src-wf) ghbi[⇒]model x∈src x∈src ghb[xx]
  in ax-model refl model⁺[xx]
  where
  ord[⇒]ppo : Rel[⇒] (Ord src-tex) Ppo
  ord[⇒]ppo x∈src y∈src (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) =
    ppo₀ ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  ord[⇒]ppo x∈src y∈src (ord-rr ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-rr ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , R[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-rw ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-rw ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-rm ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)))

  ord[⇒]ppo x∈src y∈src (ord-wr ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-wr ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , R[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-ww ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-wm ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-wm ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)))

  ord[⇒]ppo x∈src y∈src (ord-mr ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-mr ((refl , RW[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , R[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-mw ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-mw ((refl , RW[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-r)))
  ord[⇒]ppo x∈src y∈src (ord-mm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ppo₄ (fob-mm ((refl , RW[⇒] x∈src x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fₜ[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)))

  -- This is a strange case. We use the fact that the RMW's write event has
  -- an ACQ annotation.
  -- (Alternatively, we could divert the cycle to the corresponding RMW read)
  ord[⇒]ppo x∈src y∈src (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let x-acq = rmwʳ-acq (rmwʳ[⇒] x∈src x∈rmwʳ)
    in ppo₅ ((refl , x-acq) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw))

  -- our only atomic writes are produced by RMWs with ACQ + REL flags
  ord[⇒]ppo x∈src y∈src (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₐ))) =
    let yᵗ-wₐ = Wₜ[⇒] y∈src y-wₐ
        y∈dst = events[⇒] y∈src
    in ppo₆ ((refl , RW[⇒] x∈src x-rw) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , wₐ-rel y∈dst yᵗ-wₐ))

  -- our only atomic reads are produced by RMWs with ACQ + REL flags
  ord[⇒]ppo x∈src y∈src (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let x∈dst = events[⇒] x∈src
        xᵗ-rwₐ = rwₐ-acq x∈dst (rₜ⇒rwₜ (Rₜ[⇒] x∈src x-rₐ))
    in ppo₅ ((refl , xᵗ-rwₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw))
  
  ghbi[⇒]model : Rel[⇒] (Ghbi src-tex) ( co dst ∪₂ rfe dst ∪₂ fr dst ∪₂ Ppo )
  ghbi[⇒]model x∈src y∈src (ghbi-ord ord[xy]) = opf₄ (ord[⇒]ppo x∈src y∈src ord[xy])
  ghbi[⇒]model x∈src y∈src (ghbi-rfe (rfe[xy] ⨾[ _ ]⨾ (refl , _))) =
    opt₂ (rfe[⇒] x∈src y∈src rfe[xy])
  ghbi[⇒]model x∈src y∈src (ghbi-coe (coe[xy] ⨾[ _ ]⨾ (refl , _))) =
    opt₁ (co[⇒] x∈src y∈src (proj₁ coe[xy]))
  ghbi[⇒]model x∈src y∈src (ghbi-fre (fre[xy] ⨾[ _ ]⨾ (refl , _))) =
    opt₃ (fr[⇒] x∈src y∈src (proj₁ fre[xy]))


-- # Result

src-consistent : IsAIMMConsistent src-tex
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
