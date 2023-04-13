{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import Arch.Mixed using (MixedExecution)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Consistent
  {dst : Execution {arch-TCG}}
  {dst-tex : MixedExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst-tex)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to ⊎[_,_])
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _++_; _∷ʳ_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.TCG as TCG
open import Arch.X86 as X86
open import Helpers

open import Proof.Mapping.X86toTCG.Execution dst-wf dst-ok as Ex -- defines δ
open import Proof.Mapping.Mixed dst-tex δ
open import Arch.Mixed as Mixed
open Mixed.Derived src-mex

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

src-ax-internal : Acyclic _≡_ ( po-loc src ∪₂ Ca src-mex ∪₂ rf src )
src-ax-internal refl coh[xx] =
  let x∈src = ⁺-lift-predˡ cohˡ∈src coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohˡ∈src coh[⇒] x∈src x∈src coh[xx])
  where
  caˡ∈src : ∀ {x y : EventX86} → Ca src-mex x y → x ∈ events src
  caˡ∈src (ca-fr fr[xy]) = frˡ∈src fr[xy]
  caˡ∈src (ca-co co[xy]) = coˡ∈src co[xy]
  
  cohˡ∈src : ∀ {x y : EventX86} → ( po-loc src ∪₂ Ca src-mex ∪₂ rf src ) x y → x ∈ events src
  cohˡ∈src (opt₁ po-loc[xy]) = poˡ∈src (proj₁ po-loc[xy])
  cohˡ∈src (opt₂ ca[xy])     = caˡ∈src ca[xy]
  cohˡ∈src (opf₃ rf[xy])     = rfˡ∈src rf[xy]

  ca[⇒] : Rel[⇒] (Ca src-mex) (Coh dst-tex)
  ca[⇒] x∈src y∈src (ca-fr fr[xy]) = coh-fr (fr[⇒] x∈src y∈src fr[xy])
  ca[⇒] x∈src y∈src (ca-co co[xy]) = coh-co (co[⇒] x∈src y∈src co[xy])

  coh[⇒] : Rel[⇒] ( po-loc src ∪₂ Ca src-mex ∪₂ rf src ) (Coh dst-tex)
  coh[⇒] x∈src y∈src (opt₁ po-loc[xy]) = coh-po-loc (po-loc[⇒] x∈src y∈src po-loc[xy])
  coh[⇒] x∈src y∈src (opt₂ ca[xy])     = ca[⇒] x∈src y∈src ca[xy]
  coh[⇒] x∈src y∈src (opf₃ rf[xy])     = coh-rf (rf[⇒] x∈src y∈src rf[xy])
  

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

-- This is the most annoying case, for two main reasons:
--
-- * The x86 model contains a redundant case: `lob-rmwˡ`. Here, we demonstrate it
--   is redundant, before mapping to TCG. To do so, we divert chains from `dom rmw`
--   to the corresponding `codom rmw`. (In particular, see `rmwˡ-detour` below)
--
-- * The x86 model has an alternative formulation of xppo (x86 preserved program
--   order), which is: `po \ (⦗W⦘ ⨾ po ⨾ ⦗R⦘)`. It also includes fences; e.g.,
--   `(⦗F⦘ ⨾ po ⨾ ⦗R⦘) ⊆ (po \ (⦗W⦘ ⨾ po ⨾ ⦗R⦘))`. We need to divert the chains from
--   the fences, to be only between Read/Write events.
--
--
-- The main proof structure is:
--
-- * Rotate the chain, such that it starts at a Write event.
--   We need our chain to *end* at a Write, because `M × W` is trivially in xppo.
--   If the chain ended at a Read, we'd have trouble with the `W × R` case.
--   (see `rotate-w`)
--
-- * Ensure `lob` cycles are only between Read/Write events.
--   Internally, `lob` chain could have a fence in-between. However, we know it
--   is then always followed by another `lob`; That is: `lob ⨾ ⦗F⦘ ⨾ lob`. A `lob`
--   chain is always followed by a `obs` (rfe/coe/fre) at some point, which starts
--   at a Read or Write event. (See `Obmᵢ` and `ob⇒obm`).
--
-- * Map to our representation without `rmwˡ` and cleaner xppo (without fences).
--   (See `Obaᵢ` and `obm⇒oba`)
--
-- * Map to a corresponding `ghb` chain in TCG. As that `ghb` chain is impossible,
--   so is our initial `ob` chain in X86.


open MixedExecution src-mex
open TransClosure

obsˡ-rw : {x y : EventX86} → Obs src-mex x y → EvRW x
obsˡ-rw (obs-rfe rfe[xy]) = w⇒rw (×₂-applyˡ (rfe-w×r src-wf) rfe[xy])
obsˡ-rw (obs-fre fre[xy]) = r⇒rw (×₂-applyˡ (fre-r×w src-wf) fre[xy])
obsˡ-rw (obs-coe coe[xy]) = w⇒rw (×₂-applyˡ (coe-w×w src-wf) coe[xy])

obsʳ-rw : {x y : EventX86} → Obs src-mex x y → EvRW y
obsʳ-rw (obs-rfe rfe[xy]) = r⇒rw (×₂-applyʳ (rfe-w×r src-wf) rfe[xy])
obsʳ-rw (obs-fre fre[xy]) = w⇒rw (×₂-applyʳ (fre-r×w src-wf) fre[xy])
obsʳ-rw (obs-coe coe[xy]) = w⇒rw (×₂-applyʳ (coe-w×w src-wf) coe[xy])

lobi⇒po : {x y : EventX86} → Lobi src-mex x y → po src x y
lobi⇒po (lob-po (po[xy] , _)) = proj₁ po[xy]
lobi⇒po (lob-f ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , _))) =
  po-trans src-wf po[xy] po[yz]
lobi⇒po (lob-rmwˡ ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
lobi⇒po (lob-rmwʳ ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]

lob⇒po : {x y : EventX86} → lob src-mex x y → po src x y
lob⇒po = ⁺-join-trans (po-trans src-wf) ∘ ⁺-map Function.id lobi⇒po

obsi-rw : {x y : EventX86} → ( Obs src-mex ⨾ si ) x y → EvW x ⊎ EvW y
obsi-rw (obs-fre fre[xz] ⨾[ _ ]⨾ si[zy]) =
  let z-w = ×₂-applyʳ (fr-r×w src-wf) (proj₁ fre[xz])
  in opf₂ (siʳ-w z-w si[zy])
obsi-rw (obs-rfe rfe[xz] ⨾[ _ ]⨾ si[zy]) = inj₁ (×₂-applyˡ (rf-w×r src-wf) (proj₁ rfe[xz]))
obsi-rw (obs-coe coe[xz] ⨾[ _ ]⨾ si[zy]) = opt₁ (×₂-applyˡ (co-w×w src-wf) (proj₁ coe[xz]))

-- the new formulation of `xppo` could start at a fence. we avoid this by
-- rotating the cycle to start at a write
rotate-w : {x : EventX86} → ob src-mex x x → ∃[ y ] EvW y × ob src-mex y y
rotate-w [ ob-obs obsi[xx] ] with obsi-rw obsi[xx]
... | opt₁ x-w = _ , x-w , [ ob-obs obsi[xx] ]
... | opf₂ x-w = _ , x-w , [ ob-obs obsi[xx] ]
rotate-w [ ob-lob lob[xx] ] = ⊥-elim (po-irreflexive src-wf refl (lob⇒po lob[xx]))
rotate-w (ob-obs (obsi[xy]) ∷ ob[yx]) with obsi-rw obsi[xy]
... | opt₁ x-w = _ , x-w , (ob-obs obsi[xy] ∷ ob[yx])
... | opf₂ y-w = _ , y-w , (ob[yx] ∷ʳ ob-obs obsi[xy])
rotate-w {x} (ob-lob lob[xy] ∷ ob[yx]) = step lob[xy] ob[yx]
  where
  step : {y : EventX86} → lob src-mex x y → ob src-mex y x → ∃[ y ] EvW y × ob src-mex y y
  step lob[xy] [ ob-obs obsi[yx] ] with obsi-rw obsi[yx]
  ... | inj₁ y-w = _ , y-w , ob-obs obsi[yx] ∷ [ ob-lob lob[xy] ]
  ... | inj₂ x-w = _ , x-w , ob-lob lob[xy] ∷ [ ob-obs obsi[yx] ]
  step lob[xy] [ ob-lob lob[yx] ] = ⊥-elim (po-irreflexive src-wf refl (lob⇒po (lob[xy] ++ lob[yx])))
  step lob[xy] ( ob-obs obsi[yz] ∷ ob[zx] ) with obsi-rw obsi[yz]
  ... | opt₁ y-w = _ , y-w , (ob-obs obsi[yz] ∷ ob[zx]) ∷ʳ ob-lob lob[xy]
  ... | opf₂ z-w = _ , z-w , ((ob[zx] ∷ʳ ob-lob lob[xy]) ∷ʳ ob-obs obsi[yz])
  step lob[xy] ( ob-lob lob[yz] ∷ ob[zx] ) = step (lob[xy] ++ lob[yz]) ob[zx]

-- | Alternative representation of `Obi` (ob immediate), where `lob` chains are
-- always between Read/Write events.
data Obmᵢ (x y : EventX86) : Set where
  obm-obs : ( Obs src-mex ⨾ si ) x y → Obmᵢ x y
  obm-lob : ( ⦗ EvRW ⦘ ⨾ lob src-mex ⨾ ⦗ EvRW ⦘ ) x y → Obmᵢ x y

obm = TransClosure Obmᵢ

open import Relation.Nullary using (¬_)

dec-rw : (x : EventX86) → EvRW x ⊎ ¬ EvRW x
dec-rw (event-init x x₁ x₂) = opt₁ ev-init
dec-rw (event-skip x x₁) = opf₂ (λ ())
dec-rw (event-r x x₁ x₂ x₃ x₄) = opt₁ ev-r
dec-rw (event-w x x₁ x₂ x₃ x₄) = opt₁ ev-w
dec-rw (event-f x x₁ x₂) = opf₂ (λ ())

-- | Ensures `lob` cycles are only between Read/Write events.
ob⇒obm : {x y : EventX86} → EvRW x → EvRW y → ob src-mex x y → obm x y
ob⇒obm x-rw y-rw [ ob-obs (obs[xz] ⨾[ _ ]⨾ si[zy]) ] = [ obm-obs (obs[xz] ⨾[ _ ]⨾ si[zy]) ]
ob⇒obm x-rw y-rw [ ob-lob lob[xy] ] = [ obm-lob ((refl , x-rw) ⨾[ _ ]⨾ lob[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
ob⇒obm x-rw y-rw (ob-obs (obs[xv] ⨾[ _ ]⨾ si[vz]) ∷ ob[zy]) =
  let z-rw = siʳ-rw (obsʳ-rw obs[xv]) si[vz]
  in obm-obs (obs[xv] ⨾[ _ ]⨾ si[vz]) ∷ ob⇒obm z-rw y-rw ob[zy]
ob⇒obm {x} {y} x-rw y-rw (_∷_ {_} {v} (ob-lob lob[xv]) ob[zy]) with dec-rw v
... | opt₁  v-rw = obm-lob ((refl , x-rw) ⨾[ _ ]⨾ lob[xv] ⨾[ _ ]⨾ (refl , v-rw)) ∷ ob⇒obm v-rw y-rw ob[zy]
... | opf₂ ¬v-rw = step ¬v-rw lob[xv] ob[zy]
  where
  step : {v : EventX86} → ¬ EvRW v → lob src-mex x v → ob src-mex v y → obm x y
  step ¬v-rw lob[xv] [ ob-obs (obs[vz] ⨾[ _ ]⨾ _) ] = ⊥-elim (¬v-rw (obsˡ-rw obs[vz]))
  step ¬v-rw lob[xv] [ ob-lob lob[vy] ] =
    [ obm-lob ((refl , x-rw) ⨾[ _ ]⨾ (lob[xv] ++ lob[vy]) ⨾[ _ ]⨾ (refl , y-rw)) ]
  step ¬v-rw lob[xv] (ob-obs (obs[vp] ⨾[ _ ]⨾ _) ∷ _) = ⊥-elim (¬v-rw (obsˡ-rw obs[vp]))
  step ¬v-rw lob[xv] (_∷_ {_} {z} (ob-lob lob[vz]) ob[zy]) with dec-rw z
  ... | opt₁  z-rw =
    obm-lob ((refl , x-rw) ⨾[ _ ]⨾ (lob[xv] ++ lob[vz]) ⨾[ _ ]⨾ (refl , z-rw)) ∷ ob⇒obm z-rw y-rw ob[zy]
  ... | opf₂ ¬z-rw = step ¬z-rw (lob[xv] ++ lob[vz]) ob[zy]

data Xppo (x y : EventX86) : Set where
  xppo-r×m : (⦗ EvR ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘) x y → Xppo x y
  xppo-w×w : (⦗ EvW ⦘ ⨾ po src ⨾ ⦗ EvW ⦘)  x y → Xppo x y

-- | Alternative locally-ordered-before (lob) immediate
--
-- Basically, we remove the `lob-rmwˡ` case, and clean up `xppo`
data Lobaᵢ (x y : EventX86) : Set where
  loba-xppo   : Xppo                                              x y → Lobaᵢ x y
  loba-f      : ( ⦗ EvW ⦘ ⨾ po src ⨾ ⦗ EvF ⦘ ⨾ po src ⨾ ⦗ EvR ⦘ ) x y → Lobaᵢ x y
  loba-rmwʳ   : ( ⦗ codom (rmw src) ⦘ ⨾ po src ⨾ ⦗ EvR ⦘ )        x y → Lobaᵢ x y

loba = TransClosure Lobaᵢ

-- | Alternative ordered-before (ob) immediate
--
-- Basically, we remove the `lob-rmwˡ` case, and clean up `xppo`
data Obaᵢ (x y : EventX86) : Set where
  oba-obs : ( Obs src-mex ⨾ si ) x y → Obaᵢ x y
  oba-lob : loba                 x y → Obaᵢ x y

oba = TransClosure Obaᵢ

BadXppo = po-no-skip src \₂ (⦗ EvW ⦘ ⨾ po src ⨾ ⦗ EvR ⦘)

bad⇒xppo : {x y : EventX86} → EvRW x → EvRW y → BadXppo x y → Xppo x y
bad⇒xppo x-rw y-rw (po[xy] , ¬WxRy) with rw/rw x-rw | rw/rw y-rw
... | inj₁ x-r | _ = xppo-r×m ((refl , x-r) ⨾[ _ ]⨾ proj₁ po[xy] ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-w | inj₁ y-r = ⊥-elim (¬WxRy ((refl , x-w) ⨾[ _ ]⨾ proj₁ po[xy] ⨾[ _ ]⨾ (refl , y-r)))
... | inj₂ x-w | inj₂ y-w = xppo-w×w ((refl , x-w) ⨾[ _ ]⨾ proj₁ po[xy] ⨾[ _ ]⨾ (refl , y-w))

xppo-m×w : {x y : EventX86} → EvRW x → EvW y → po src x y → Xppo x y
xppo-m×w x-rw y-w po[xy] with rw/rw x-rw
... | inj₁ x-r = xppo-r×m ((refl , x-r) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , w⇒rw y-w))
... | inj₂ x-w = xppo-w×w ((refl , x-w) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-w))

lob⇒loba-w : {x y : EventX86} → EvRW x → EvW y → lob src-mex x y → loba x y
lob⇒loba-w x-rw y-w lob[xy] = [ loba-xppo (xppo-m×w x-rw y-w (lob⇒po lob[xy])) ]

open Relation.Binary.Tri

ext-po : {x y z : EventX86}
  → ¬ EvInit x
  → ext src x y
  → po src x z
  → ext src y z
ext-po ¬x-init ext-xy po[xz] (inj₁ po[yz]) with unsplit-po-triʳ src-wf po[xz] po[yz]
... | tri< po[xy] _ _ = ext-xy (opt₁ po[xy])
... | tri≈ _  x≡y   _ = ext-xy (opf₃ x≡y)
... | tri> _ _ po[yx] = ext-xy (opt₂ po[yx])
ext-po ¬x-init ext-xy po[xz] (opt₂ po[zy]) =
  let po[xy] = po-trans src-wf po[xz] po[zy]
  in ext-xy (opt₁ po[xy])
ext-po ¬x-init ext-xy po[xz] (opf₃ refl) = ext-xy (opt₁ po[xz])

sym-ext : {x y : EventX86} → ext src x y → ext src y x
sym-ext ext-xy (opt₁ po[yx]) = ext-xy (opt₂ po[yx])
sym-ext ext-xy (opt₂ po[xy]) = ext-xy (opt₁ po[xy])
sym-ext ext-xy (opf₃ y≡x) = ext-xy (opf₃ (≡-sym y≡x))

rmwˡ-detour : {x y : EventX86} → ( ⦗ dom (rmw src) ⦘ ⨾ fre src ) x y → ( rmw src ⨾ coe src ) x y
rmwˡ-detour {x} {y} ((refl , (z , rmw[xz])) ⨾[ _ ]⨾ fre[xy]@(rf⁻¹[xv] ⨾[ _ ]⨾ co[vy] , ext-xy)) =
  let zx-sloc = sym-same-loc (⊆₂-apply (rmw-sloc src-wf) rmw[xz])
      xy-sloc = ⊆₂-apply (fr-sloc src-wf) (proj₁ fre[xy])
      zy-sloc = trans-same-loc zx-sloc xy-sloc
      z-w = wₜ⇒w (×₂-applyʳ (rmw-r×w src-wf) rmw[xz])
      y-w = ×₂-applyʳ (co-w×w src-wf) co[vy]
      z-has-loc = w-has-loc z-w
      y-has-loc = subst-sloc zy-sloc z-has-loc
      z∈src = rmwʳ∈ex src-wf rmw[xz]
      y∈src = coʳ∈ex src-wf co[vy]
      z-pred : WithPred (EvW ∩₁ HasLoc _ ∩₁ events src)
      z-pred = with-pred z (z-w , z-has-loc , z∈src)
      y-pred : WithPred (EvW ∩₁ HasLoc _ ∩₁ events src)
      y-pred = with-pred y (y-w , y-has-loc , y∈src)
      po[xz] = proj₁ (⊆₂-apply (rmw-def src-wf) rmw[xz])
      x-r = rₜ⇒r (×₂-applyˡ (rmw-r×w src-wf) rmw[xz])
      ¬x-init = λ{x-init → disjoint-r/init _ (x-r , x-init)}
      ext-yz = ext-po ¬x-init ext-xy po[xz]
  in
  case co-tri src-wf _ z-pred y-pred of
  λ{ (tri< co[zy] _ _) → rmw[xz] ⨾[ _ ]⨾ (co[zy] , sym-ext ext-yz)
   ; (tri≈ _ with-z≡y _) →
       case with-pred-≡ with-z≡y of λ{refl → ⊥-elim (ext-xy (inj₁ po[xz]))}
   ; (tri> _ _ co[yz]) →
       ⊥-elim (src-ax-atomicity _ _ (rmw[xz] , fre[xy] ⨾[ _ ]⨾ (co[yz] , ext-yz)))
   }

fence-po : {x y z : EventX86}
  → EvRW x
  → po src x y
  → EvF y
  → po src y z
  → EvRW z
  → Lobaᵢ x z
fence-po x-rw po[xy] y-f po[yz] z-rw
  with rw/rw x-rw | rw/rw z-rw
... | inj₁ x-r | _        =
  loba-xppo (xppo-r×m ((refl , x-r) ⨾[ _ ]⨾ po-trans src-wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , z-rw)))
... | inj₂ x-w | inj₁ z-r =
  loba-f ((refl , x-w) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-r))
... | inj₂ x-w | inj₂ z-w =
  loba-xppo (xppo-w×w ((refl , x-w) ⨾[ _ ]⨾ po-trans src-wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , z-w)))


ev-rw/f : (x : EventX86) → (EvRW ∪₁ EvF ∪₁ EvSkip) x
ev-rw/f (event-init _ _ _)  = opt₁ ev-init
ev-rw/f (event-skip _ _)    = opf₃ ev-skip
ev-rw/f (event-r _ _ _ _ _) = opt₁ ev-r
ev-rw/f (event-w _ _ _ _ _) = opt₁ ev-w
ev-rw/f (event-f _ _ _)     = opt₂ ev-f


lob⇒oba-r : {x y : EventX86}
  → EvRW x
  → lob src-mex x y
  → {z : EventX86}
  → (fre src ⨾ si) y z
  → oba x z
lob⇒oba-r x-rw [ lob-po xppo[xy] ] (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  let y-rw = r⇒rw (×₂-applyˡ (fr-r×w src-wf) (proj₁ fre[yv]))
  in oba-lob [ loba-xppo (bad⇒xppo x-rw y-rw xppo[xy]) ] ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
lob⇒oba-r x-rw [ lob-f τ ] (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  oba-lob [ loba-f τ ] ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
lob⇒oba-r _ [ lob-rmwˡ ((refl , x-w) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] (fre[yv] ⨾[ v ]⨾ si[vz])
  with rmwˡ-detour ((refl , y∈rmwˡ) ⨾[ _ ]⨾ fre[yv])
... | (rmw[yq] ⨾[ _ ]⨾ coe[qv]) =
  let q-w = wₜ⇒w (rmwʳ-w src-wf (_ , rmw[yq]))
      po[yq] = proj₁ (⊆₂-apply (rmw-def src-wf) rmw[yq])
      po[xq] = po-trans src-wf po[xy] po[yq]
  in oba-lob [ loba-xppo (xppo-w×w ((refl , x-w) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-w))) ]
       ∷ [ oba-obs (obs-coe coe[qv] ⨾[ _ ]⨾ si[vz]) ]
lob⇒oba-r x-rw [ lob-rmwʳ τ ] (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  oba-lob [ loba-rmwʳ τ ] ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
lob⇒oba-r x-rw (_∷_ {_} {q} (lob-po xppo[xq]) lob[qy]) (fre[yv] ⨾[ _ ]⨾ si[vz])
  with ev-rw/f q
... | opt₁ q-rw   = oba-lob [ loba-xppo (bad⇒xppo x-rw q-rw xppo[xq]) ] ∷ lob⇒oba-r q-rw lob[qy] (fre[yv] ⨾[ _ ]⨾ si[vz])
... | opt₂ q-f    =
  let y-r = ×₂-applyˡ (fr-r×w src-wf) (proj₁ fre[yv])
  in oba-lob [ fence-po x-rw (proj₁ (proj₁ xppo[xq])) q-f (lob⇒po lob[qy]) (r⇒rw y-r) ] ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
... | opf₃ q-skip =
  let ¬q-skip = proj₂ (proj₂ (proj₁ xppo[xq]))
  in ⊥-elim (¬q-skip q-skip)
lob⇒oba-r x-rw (lob-f ((refl , x-w) ⨾[ _ ]⨾ po[xt] ⨾[ _ ]⨾ (refl , t-f) ⨾[ _ ]⨾ po[tq] ⨾[ _ ]⨾ (refl , q-r)) ∷ lob[qy]) (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  let y-r = ×₂-applyˡ (fr-r×w src-wf) (proj₁ fre[yv])
  in oba-lob [ loba-f ((refl , x-w) ⨾[ _ ]⨾ po[xt] ⨾[ _ ]⨾ (refl , t-f) ⨾[ _ ]⨾ po-trans src-wf po[tq] (lob⇒po lob[qy]) ⨾[ _ ]⨾ (refl , y-r)) ]
       ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
lob⇒oba-r {_} {y} _ (lob-rmwˡ ((refl , x-w) ⨾[ _ ]⨾ po[xq] ⨾[ q ]⨾ (refl , q∈rmwˡ)) ∷ lob[qy]) (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  -- previously we went through `dom rmw`. we now go through the corresponding `codom rmw`
  -- because x is a write, and `codom rmw` is a write, it is in xppo (W×W)
  -- `codom rmw` is then ordered with `y`, because of `lob-rmwʳ`
  let (t , rmw[qt]) = q∈rmwˡ
      pi[qt] = ⊆₂-apply (rmw-def src-wf) rmw[qt]
      po[qy] = lob⇒po lob[qy]
      y-r = ×₂-applyˡ (fr-r×w src-wf) (proj₁ fre[yv])
      t-w = wₜ⇒w (×₂-applyʳ (rmw-r×w src-wf) rmw[qt])
      q-r = rₜ⇒r (×₂-applyˡ (rmw-r×w src-wf) rmw[qt])
      ¬q-init : ¬ EvInit q
      ¬q-init = λ{q-init → disjoint-r/init _ (q-r , q-init)}
  in
  case unsplit-poˡ src-wf ¬q-init po[qy] pi[qt] of
  λ{ (inj₁ refl) → ⊥-elim (disjoint-r/w _ (y-r , t-w))
   ; (inj₂ po[ty]) →
       oba-lob (loba-xppo (xppo-w×w ((refl , x-w) ⨾[ _ ]⨾ po-trans src-wf po[xq] (proj₁ pi[qt]) ⨾[ _ ]⨾ (refl , t-w)))
                  ∷ [ loba-rmwʳ ((refl , (_ , rmw[qt])) ⨾[ _ ]⨾ po[ty] ⨾[ _ ]⨾ (refl , y-r)) ])
       ∷ [ oba-obs (obs-fre fre[yv] ⨾[ _ ]⨾ si[vz]) ]
   }
lob⇒oba-r x-rw (lob-rmwʳ lob[xq]@(_ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ (refl , q-r)) ∷ lob[qy]) (fre[yv] ⨾[ _ ]⨾ si[vz]) =
  oba-lob [ loba-rmwʳ lob[xq] ] ∷ lob⇒oba-r (r⇒rw q-r) lob[qy] (fre[yv] ⨾[ _ ]⨾ si[vz])


obm⇒oba : {x y : EventX86} → EvW y → obm x y → oba x y
obm⇒oba y-w [ obm-obs obs⨾si[xy] ] = [ oba-obs obs⨾si[xy] ]
obm⇒oba y-w [ obm-lob ((refl , x-rw) ⨾[ _ ]⨾ lob[xy] ⨾[ _ ]⨾ (refl , _)) ] =
  [ oba-lob (lob⇒loba-w x-rw y-w lob[xy]) ]
obm⇒oba y-w (obm-obs obs⨾si[xz] ∷ obm[zy]) =
  oba-obs obs⨾si[xz] ∷ obm⇒oba y-w obm[zy]
obm⇒oba {x} {y} y-w (obm-lob ((refl , x-rw) ⨾[ _ ]⨾ lob[xz] ⨾[ _ ]⨾ (refl , z-rw)) ∷ obm[zy])
  with rw/rw z-rw
... | inj₁ z-r = step lob[xz] z-r obm[zy]
  where
  step : {z : EventX86} → lob src-mex x z → EvR z → obm z y → oba x y
  step lob[xz] z-r [ obm-obs (obs-fre fre[zv] ⨾[ _ ]⨾ si[vy]) ] =
    lob⇒oba-r x-rw lob[xz] (fre[zv] ⨾[ _ ]⨾ si[vy])
  step lob[xz] z-r [ obm-obs (obs-rfe rfe[zv] ⨾[ _ ]⨾ si[vy]) ] =
    ⊥-elim (disjoint-r/w _ (z-r , ×₂-applyˡ (rf-w×r src-wf) (proj₁ rfe[zv])))
  step lob[xz] z-r [ obm-obs (obs-coe coe[zv] ⨾[ _ ]⨾ si[vy]) ] =
    ⊥-elim (disjoint-r/w _ (z-r , ×₂-applyˡ (co-w×w src-wf) (proj₁ coe[zv])))
  step lob[xz] z-r [ obm-lob ((refl , _) ⨾[ _ ]⨾ lob[zy] ⨾[ _ ]⨾ (refl , _)) ] =
    [ oba-lob (lob⇒loba-w x-rw y-w (lob[xz] ++ lob[zy])) ]
  step lob[xz] z-r (obm-obs (obs-fre fre[zv] ⨾[ _ ]⨾ si[vk]) ∷ obm[ky]) =
    lob⇒oba-r x-rw lob[xz] (fre[zv] ⨾[ _ ]⨾ si[vk]) ++ obm⇒oba y-w obm[ky]
  step lob[xz] z-r (obm-obs (obs-rfe rfe[zv] ⨾[ _ ]⨾ si[vk]) ∷ obm[ky]) =
    ⊥-elim (disjoint-r/w _ (z-r , ×₂-applyˡ (rf-w×r src-wf) (proj₁ rfe[zv])))
  step lob[xz] z-r (obm-obs (obs-coe coe[zv] ⨾[ _ ]⨾ si[vk]) ∷ obm[ky]) =
    ⊥-elim (disjoint-r/w _ (z-r , ×₂-applyˡ (co-w×w src-wf) (proj₁ coe[zv])))
  step lob[xz] z-r (obm-lob ((refl , _) ⨾[ _ ]⨾ lob[zv] ⨾[ v ]⨾ (refl , v-rw)) ∷ obm[vy])
    with rw/rw v-rw
  ... | opt₁ v-r = step (lob[xz] ++ lob[zv]) v-r obm[vy]
  ... | opf₂ v-w = oba-lob (lob⇒loba-w x-rw v-w (lob[xz] ++ lob[zv])) ∷ obm⇒oba y-w obm[vy]
... | inj₂ z-w = oba-lob (lob⇒loba-w x-rw z-w lob[xz]) ∷ obm⇒oba y-w obm[zy]


-- # xppo
xppo[⇒]ord : Rel[⇒] Xppo (Ord dst-tex)

-- ## R × M
xppo[⇒]ord x∈src y∈src (xppo-r×m ((refl , x-r) ⨾[ x@(event-r _ _ _ _ (lab-r tmov)) ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  ord-rm lemma
  where
  lemma : ( ⦗ EvR ⦘ ⨾ po dst ⨾ ⦗ EvFₜ RM ⦘ ⨾ po dst ⨾ ⦗ EvRW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
  lemma with splitˡ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy])
  lemma | inj₁ pi[xy] with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
  lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xy] pi[xz]
  lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f | refl = ⊥-elim (disjoint-f/rw z (fₜ⇒f z-is-f , RW[⇒] y∈src y-rw))
  lemma | inj₂ (z  , pi[xz] , po[zy]) with r-f-po₁ (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r refl))
  lemma | inj₂ (z  , pi[xz] , po[zy]) | w , pi[xw] , w-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xw] pi[xz]
  lemma | inj₂ (.w , pi[xw] , po[wy]) | w , _ , w-is-f | refl =
    (refl , R[⇒] x∈src ev-r) ⨾[ _ ]⨾ proj₁ pi[xw] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ po[wy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)
    
xppo[⇒]ord x∈src y∈src (xppo-r×m ((refl , x-r) ⨾[ x@(event-r _ _ _ _ (lab-r trmw)) ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  ord-r ((refl , Rₜ[⇒] x∈src (ev-r refl)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw))

-- # W × W

xppo[⇒]ord x∈src y∈src (xppo-w×w ((refl , x-w) ⨾[ x ]⨾ po[xy] ⨾[ y@(event-w _ _ _ _ (lab-w tmov)) ]⨾ (refl , y-w))) =
  ord-ww lemma
  where
  lemma : ( ⦗ EvW ⦘  ⨾ po dst ⨾ ⦗ EvFₜ WW ⦘ ⨾ po dst ⨾ ⦗ EvW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
  lemma with splitʳ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy]) |  f-w-po₁ {ev[⇒] y∈src} (events[⇒] y∈src) (Wₜ[⇒] y∈src (ev-w refl))
  lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f with po-immˡ dst-wf pi[zy] pi[xy]
  lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f | refl = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-is-f , W[⇒] x∈src x-w))
  lemma | inj₂ (z , po[xz] , pi[zy]) | w , pi[wy] , w-is-f with po-immˡ dst-wf pi[zy] pi[wy]
  lemma | inj₂ (.w , po[xz] , pi[zy]) | w , pi[wy] , w-is-f | refl =
    (refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ proj₁ pi[wy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w)

xppo[⇒]ord x∈src y∈src (xppo-w×w ((refl , x-w) ⨾[ x ]⨾ po[xy] ⨾[ y@(event-w _ _ _ _ (lab-w trmw)) ]⨾ (refl , y-w))) =
  ord-w ((refl , RW[⇒] x∈src (w⇒rw x-w)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (ev-w refl)))

xppo[⇒]ord x∈src y∈src (xppo-w×w ((refl , x-w) ⨾[ x@(event-init _ _ _) ]⨾ po[xy] ⨾[ y@(event-init _ _ _) ]⨾ (refl , y-w))) =
  ord-init ((refl , Init[⇒] x∈src ev-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src (w⇒rw y-w)))

xppo[⇒]ord x∈src y∈src (xppo-w×w ((refl , x-w) ⨾[ x@(event-w _ _ _ _ _) ]⨾ po[xy] ⨾[ y@(event-init _ _ _) ]⨾ (refl , y-w))) =
  ⊥-elim (absurd (po-init-first src-wf po[xy] ev-init) λ())


lobaᵢ[⇒]ord : Rel[⇒] Lobaᵢ (Ord dst-tex)
lobaᵢ[⇒]ord x∈src y∈src (loba-xppo xppo[xy]) = xppo[⇒]ord x∈src y∈src xppo[xy]
lobaᵢ[⇒]ord x∈src y∈src (loba-f ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) =
  let z∈src = poʳ∈src po[xz]
      po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
      po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
  in ord-mm ((refl , RW[⇒] x∈src (w⇒rw x-w)) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , F[⇒] z∈src z-f) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src (r⇒rw y-r)))
lobaᵢ[⇒]ord x∈src y∈src (loba-rmwʳ ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-r))) =
  ord-rmw-codom ((refl , rmwʳ[⇒] x∈src x∈rmwʳ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src (r⇒rw y-r)))


lobaᵢˡ∈src : {x y : EventX86} → Lobaᵢ x y → x ∈ events src
lobaᵢˡ∈src (loba-xppo (xppo-r×m ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ _))) =
  poˡ∈ex src-wf po[xy]
lobaᵢˡ∈src (loba-xppo (xppo-w×w ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ _))) =
  poˡ∈ex src-wf po[xy]
lobaᵢˡ∈src (loba-f ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ _)) =
  poˡ∈ex src-wf po[xz]
lobaᵢˡ∈src (loba-rmwʳ ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ _)) =
  poˡ∈ex src-wf po[xy]
  
obaᵢ[⇒]ghb : Rel[⇒] Obaᵢ (ghb dst-tex)
obaᵢ[⇒]ghb x∈src y∈src (oba-obs (obs-fre fre[xz] ⨾[ _ ]⨾ si[zy])) =
  let z∈src = frʳ∈ex src-wf (proj₁ fre[xz])
  in [ ghbi-fre (fre[⇒] x∈src z∈src fre[xz] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy]) ]
obaᵢ[⇒]ghb x∈src y∈src (oba-obs (obs-rfe rfe[xz] ⨾[ _ ]⨾ si[zy])) =
  let z∈src = rfʳ∈ex src-wf (proj₁ rfe[xz])
  in [ ghbi-rfe (rfe[⇒] x∈src z∈src rfe[xz] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy]) ]
obaᵢ[⇒]ghb x∈src y∈src (oba-obs (obs-coe coe[xz] ⨾[ _ ]⨾ si[zy])) =
  let z∈src = coʳ∈ex src-wf (proj₁ coe[xz])
  in [ ghbi-coe (coe[⇒] x∈src z∈src coe[xz] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy]) ]
obaᵢ[⇒]ghb x∈src y∈src (oba-lob lob[xy]) = ⁺[⇒]ˡ lobaᵢˡ∈src (λ a∈src b∈src loba[ab] → ghbi-ord (lobaᵢ[⇒]ord a∈src b∈src loba[ab])) x∈src y∈src lob[xy]

obaᵢˡ∈src : {x y : EventX86} → Obaᵢ x y → x ∈ events src
obaᵢˡ∈src (oba-obs (obs-fre fre[xz] ⨾[ _ ]⨾ _)) = frˡ∈ex src-wf (proj₁ fre[xz])
obaᵢˡ∈src (oba-obs (obs-rfe rfe[xz] ⨾[ _ ]⨾ _)) = rfˡ∈ex src-wf (proj₁ rfe[xz])
obaᵢˡ∈src (oba-obs (obs-coe coe[xz] ⨾[ _ ]⨾ _)) = coˡ∈ex src-wf (proj₁ coe[xz])
obaᵢˡ∈src (oba-lob lob[xz]) = ⁺-lift-predˡ lobaᵢˡ∈src lob[xz]

oba[⇒]ghb : Rel[⇒] oba (ghb dst-tex)
oba[⇒]ghb x∈src y∈src oba[xy] = ⁺-join (⁺[⇒]ˡ obaᵢˡ∈src obaᵢ[⇒]ghb x∈src y∈src oba[xy])

src-ax-external : Irreflexive _≡_ (ob src-mex)
src-ax-external refl ob[xx] =
  let -- Rotate the cycle such that it starts at a write event
      (y , y-w , ob[yy]) = rotate-w ob[xx]
      -- Ensure `lob` chains are only between read/write events
      obm[yy] = ob⇒obm (w⇒rw y-w) (w⇒rw y-w) ob[yy]
      -- Remove the (redundant) `lob-rmwˡ` case.
      -- and clean up the annoying xppo representation (which also includes fences)
      oba[yy] = obm⇒oba y-w obm[yy]
      -- Map it to a TCG cycle
      y∈src = ⁺-lift-predˡ obaᵢˡ∈src oba[yy]
      ghb[yy]ᵗ = oba[⇒]ghb y∈src y∈src oba[yy]
  in ax-global-ord dst-consistent refl ghb[yy]ᵗ


-- # Result

src-consistent : IsX86Consistent src-mex
src-consistent =
  record
    { ax-internal  = src-ax-internal
    ; ax-atomicity = src-ax-atomicity
    ; ax-external  = src-ax-external
    }
