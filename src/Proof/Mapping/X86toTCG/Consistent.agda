{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Consistent
  {dst : Execution {arch-TCG}}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.TCG as TCG
open import Arch.X86 as X86
open import Helpers

open import Proof.Mapping.X86toTCG.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra


open Δ.Consistency δ

open X86.Relations
open TCG-X86Restricted dst-ok
open TCG.Relations
open IsTCGConsistent



-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result



-- # Definitions

-- # Proof: Coherence

src-ax-coherence : Acyclic _≡_ ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src )
src-ax-coherence refl coh[xx] =
  let x∈src = ⁺-lift-predˡ cohˡ∈src coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohˡ∈src coh[⇒] x∈src x∈src coh[xx])
  where
  cohˡ∈src : ∀ {x y : EventX86} → ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) x y → x ∈ events src
  cohˡ∈src (opt₁ po-loc[xy]) = poˡ∈src (proj₁ po-loc[xy])
  cohˡ∈src (opt₂ rf[xy])     = rfˡ∈src rf[xy]
  cohˡ∈src (opt₃ fr[xy])     = frˡ∈src fr[xy]
  cohˡ∈src (opf₄ co[xy])     = coˡ∈src co[xy]
  
  coh[⇒] : Rel[⇒] ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) (Coh dst)
  coh[⇒] x∈src y∈src (opt₁ po-loc[xy]) = coh-po-loc (po-loc[⇒] x∈src y∈src po-loc[xy])
  coh[⇒] x∈src y∈src (opt₂ rf[xy])     = coh-rf (rf[⇒] x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (opt₃ fr[xy])     = coh-fr (fr[⇒] x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (opf₄ co[xy])     = coh-co (co[⇒] x∈src y∈src co[xy])


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ _ ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

-- | Like `Xhb` where `rfi`, `fri`, `coi` are extracted and placed into `xppo`.
data XhbAlt (ex : Execution {arch-x86}) (x y : EventX86) : Set where
  xhba-xppo    : Xppo ex x y → XhbAlt ex x y
  xhba-implied : Implied ex x y → XhbAlt ex x y
  xhba-rfe     : rfe ex x y → XhbAlt ex x y
  xhba-fre     : fre ex x y → XhbAlt ex x y
  xhba-coe     : coe ex x y → XhbAlt ex x y

src-ax-ghb : Acyclic _≡_ (Xhb src)
src-ax-ghb = acyclic-⊆₂ proof-alt (⊆: xhb-alt)
  where
  -- This is actually bi-directional, but proving both ways is unnecessary.
  -- Intuitively, we extract: rf = rfi ∪₂ rfe , co = coi ∪₂ coe , fr = fri ∪₂ fre
  -- Then: rfi ∪₂ fri ∪₂ coi ⊆ xppo
  xhb-alt : Xhb src ⊆₂' XhbAlt src
  xhb-alt x y (xhb-xppo xppo[xy]) = xhba-xppo xppo[xy]
  xhb-alt x y (xhb-implied implied[xy]) = xhba-implied implied[xy]
  xhb-alt x y (xhb-rfe rfe[xy]) = xhba-rfe rfe[xy]
  xhb-alt x y (xhb-fr fr[xy]) with ⇔₂-apply-⊆₂ (internal⊎external src-wf (fr src)) fr[xy]
  xhb-alt x y (xhb-fr fr[xy]) | inj₂ fre[xy] = xhba-fre fre[xy]
  xhb-alt x y (xhb-fr fr[xy]) | inj₁ fri[xy]@(_ , po[xy]) with ⊆₂-apply (fr-r×w src-wf) fr[xy]
  xhb-alt x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r , ev-init with po-init-first src-wf po[xy] ev-init
  xhb-alt x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r , ev-init | ()
  xhb-alt x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r , ev-w = xhba-xppo (xppo-r×w ((ev-r , ev-w) , po[xy]))
  xhb-alt x y (xhb-co co[xy]) with ⇔₂-apply-⊆₂ (internal⊎external src-wf (co src)) co[xy]
  xhb-alt x y (xhb-co co[xy]) | inj₂ coe[xy] = xhba-coe coe[xy]
  xhb-alt x y (xhb-co co[xy]) | inj₁ coi[xy]@(_ , po[xy]) =
    let xppo[xy] = xppo-w×w (⊆₂-apply (co-w×w src-wf) {x = x} {y = y} co[xy] , po[xy])
    in xhba-xppo xppo[xy]

  -- # xppo
  xppo[⇒]ord : Rel[⇒] (Xppo src) (Ord dst)

  -- ## R × W
  xppo[⇒]ord {_} {.(event-init _ _ _)} x∈src y∈src (xppo-r×w ((ev-r , ev-init) , po[xy])) =
    absurd (po-init-first src-wf po[xy] ev-init) λ()
  
  xppo[⇒]ord {x@(event-r _ _ _ _ (lab-r tmov))} {y@(event-w _ _ _ _ (lab-w tmov))} x∈src y∈src (xppo-r×w ((ev-r , ev-w) , po[xy])) =
    ord-rm lemma
    where
    lemma : ( ⦗ EvR ⦘ ⨾ po dst ⨾ ⦗ EvFₜ RM ⦘ ⨾ po dst ⨾ ⦗ EvRW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitˡ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy])
    lemma | inj₁ pi[xy] with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xy] pi[xz]
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f | refl = ⊥-elim (disjoint-f/w z (fₜ⇒f z-is-f , W[⇒] y∈src ev-w))
    lemma | inj₂ (z  , pi[xz] , po[zy]) with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
    lemma | inj₂ (z  , pi[xz] , po[zy]) | w , pi[xw] , w-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xw] pi[xz]
    lemma | inj₂ (.w , pi[xw] , po[wy]) | w , _ , w-is-f | refl =
      (refl , R[⇒] x∈src ev-r) ⨾[ _ ]⨾ proj₁ pi[xw] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ po[wy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src ev-w)
    
  xppo[⇒]ord {x@(event-r _ _ _ _ (lab-r tmov))} {y@(event-w _ _ _ _ (lab-w trmw))} x∈src y∈src (xppo-r×w ((ev-r , ev-w) , po[xy])) =
    ord-w (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (ev-w refl)))
  
  xppo[⇒]ord {x@(event-r _ _ _ _ (lab-r trmw))} {y@(event-w _ _ _ _ (lab-w _))} x∈src y∈src (xppo-r×w ((ev-r , ev-w) , po[xy])) =
    ord-r ((refl , Rₜ[⇒] x∈src (ev-r refl)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
    
  -- ## W × W
  xppo[⇒]ord {x@(event-init _ _ _)} {y} x∈src y∈src (xppo-w×w ((ev-init , y-is-w) , po[xy])) =
    ord-init ((refl , Init[⇒] x∈src ev-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  
  xppo[⇒]ord {.(event-w _ _ _ _ _)} {.(event-init _ _ _)} x∈src y∈src (xppo-w×w ((ev-w , ev-init) , po[xy])) = 
    absurd (po-init-first src-wf po[xy] ev-init) λ()
    
  xppo[⇒]ord {x@(event-w _ _ _ _ _)} {y@(event-w _ _ _ _ (lab-w tmov))} x∈src y∈src (xppo-w×w ((ev-w , ev-w) , po[xy])) =
    ord-ww lemma
    where
    lemma : ( ⦗ EvW ⦘  ⨾ po dst ⨾ ⦗ EvFₜ WW ⦘ ⨾ po dst ⨾ ⦗ EvW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitʳ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy]) |  f-w-po₁ {ev[⇒] y∈src} (events[⇒] y∈src) (Wₜ[⇒] y∈src (ev-w refl))
    lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f with po-immˡ dst-wf pi[zy] pi[xy]
    lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f | refl = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-is-f , W[⇒] x∈src ev-w))
    lemma | inj₂ (z , po[xz] , pi[zy]) | w , pi[wy] , w-is-f with po-immˡ dst-wf pi[zy] pi[wy]
    lemma | inj₂ (.w , po[xz] , pi[zy]) | w , pi[wy] , w-is-f | refl =
      (refl , W[⇒] x∈src ev-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ proj₁ pi[wy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src ev-w)
  
  xppo[⇒]ord {x@(event-w _ _ _ _ (lab-w _))} {y@(event-w _ _ _ _ (lab-w trmw))} x∈src y∈src (xppo-w×w ((ev-w , ev-w) , po[xy])) =
    ord-w (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (ev-w refl)))

  -- ## R × R
  xppo[⇒]ord {x@(event-r _ _ _ _ (lab-r tmov))} {y@(event-r _ _ _ _ (lab-r _))} x∈src y∈src (xppo-r×r ((ev-r , ev-r) , po[xy])) =
    ord-rm lemma
    where
    lemma : ( ⦗ EvR ⦘ ⨾ po dst ⨾ ⦗ EvFₜ RM ⦘ ⨾ po dst ⨾ ⦗ EvRW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitˡ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy])
    lemma | inj₁ pi[xy] with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xy] pi[xz]
    lemma | inj₁ pi[xy] | _ , pi[xz] , z-is-f | refl = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-is-f , R[⇒] y∈src ev-r))
    lemma | inj₂ (z , pi[xz] , po[zy]) with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
    lemma | inj₂ (z , pi[xz] , po[zy]) | w , pi[xw] , w-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xw] pi[xz]
    lemma | inj₂ (.w , pi[xw] , po[wy]) | w , _ , w-is-f | refl =
      (refl , R[⇒] x∈src ev-r) ⨾[ ev[⇒] {x} x∈src ]⨾ proj₁ pi[xw] ⨾[ w ]⨾ (refl , w-is-f) ⨾[ w ]⨾ po[wy] ⨾[ ev[⇒] {y} y∈src ]⨾ (refl , RW[⇒] y∈src ev-r)

  xppo[⇒]ord {x@(event-r _ _ _ _ (lab-r trmw))} {y@(event-r _ _ _ _ (lab-r _))} x∈src y∈src (xppo-r×r ((ev-r , ev-r) , po[xy])) =
    ord-r ((refl , Rₜ[⇒] x∈src (ev-r refl)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
    
  implied[⇒]ord : Rel[⇒] (Implied src) (Ord dst)
  implied[⇒]ord {x} {y} x∈src y∈src (implied-pof (po[xy] ⨾[ y ]⨾ (refl , inj₁ y∈rmwdom@(z , rmw[yz])))) =
    let z∈src = rmwʳ∈src rmw[yz]
    in ord-rmw-dom (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , ev[⇒] {z} z∈src , rmw[⇒] y∈src z∈src rmw[yz]))
  implied[⇒]ord {x} {y} x∈src y∈src (implied-pof (po[xy] ⨾[ y ]⨾ (refl , inj₂ y-f))) =
    ord-sc₁ (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , F[⇒] y∈src y-f))
  
  implied[⇒]ord {x} {y} x∈src y∈src (implied-fpo ((refl , inj₁ x∈rmwcodom@(z , rmw[zx])) ⨾[ x ]⨾ po[xy])) =
    let z∈src = rmwˡ∈src rmw[zx]
    in ord-rmw-codom ((refl , (ev[⇒] {z} z∈src , rmw[⇒] z∈src x∈src rmw[zx])) ⨾[ ev[⇒] {x} x∈src ]⨾ po[⇒] x∈src y∈src po[xy])
  implied[⇒]ord {x} {y} x∈src y∈src (implied-fpo ((refl , inj₂ x-is-f) ⨾[ x ]⨾ po[xy])) =
    ord-sc₂ ((refl , F[⇒] x∈src x-is-f) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])

  xhba[⇒]ghbi : Rel[⇒] (XhbAlt src) (Ghbi dst)
  xhba[⇒]ghbi x∈src y∈src (xhba-xppo xppo[xy])       = ghbi-ord (xppo[⇒]ord x∈src y∈src xppo[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-implied implied[xy]) = ghbi-ord (implied[⇒]ord x∈src y∈src implied[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-rfe rfe[xy])         = ghbi-rfe (rfe[⇒] x∈src y∈src rfe[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-fre fre[xy])         = ghbi-fre (fre[⇒] x∈src y∈src fre[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-coe coe[xy])         = ghbi-coe (coe[⇒] x∈src y∈src coe[xy])

  xhbaˡ∈src : ∀ {x y : EventX86} → XhbAlt src x y → x ∈ events src
  xhbaˡ∈src (xhba-xppo (xppo-w×w (_ , po[xy]))) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-xppo (xppo-r×w (_ , po[xy]))) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-xppo (xppo-r×r (_ , po[xy]))) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-implied (implied-pof (po[xy] ⨾[ _ ]⨾ _))) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-implied (implied-fpo ((refl , _) ⨾[ _ ]⨾ po[xy]))) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-rfe (rf[xy] , _)) = rfˡ∈src rf[xy]
  xhbaˡ∈src (xhba-fre (fr[xy] , _)) = frˡ∈src fr[xy]
  xhbaˡ∈src (xhba-coe (co[xy] , _)) = coˡ∈src co[xy]

  proof-alt : Acyclic _≡_ (XhbAlt src)
  proof-alt refl xhb⁺xx = 
    let x∈src = ⁺-lift-predˡ xhbaˡ∈src xhb⁺xx
    in ax-global-ord dst-consistent refl (⁺[⇒]ˡ xhbaˡ∈src xhba[⇒]ghbi x∈src x∈src xhb⁺xx)
    

-- # Result

src-consistent : IsX86Consistent src
src-consistent =
  record
    { ax-coherence = src-ax-coherence
    ; ax-atomicity = src-ax-atomicity
    ; ax-ghb       = src-ax-ghb
    }
