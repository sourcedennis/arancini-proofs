{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8 using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8.Consistent
  {dst : Execution {arch-Armv8}}
  {dst-a8 : Armv8Execution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst-a8)
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
open import MapTCGtoArmv8
open import Arch.Armv8 as Armv8
open import Arch.TCG as TCG
open import Helpers

open import Proof.Mapping.TCGtoArmv8.Execution dst-wf dst-ok as Ex -- defines δ
open Ex.Extra


open Δ.Consistency δ

open TCG.Relations
open Armv8-TCGRestricted dst-ok
open Armv8.Relations dst-a8
open IsArmv8Consistent
open Relation.Binary.Tri

open import Proof.Mapping.Mixed (Armv8Execution.mix dst-a8) δ
open import Arch.Mixed using (MixedExecution)
-- open MixedExecution src-mex

open TCG.Properties src-mex src-wf


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- # Proof: Coherence

data Internal (x y : EventTCG) : Set where
  int-rw : ( po-loc src ⨾ rf src ) x y → Internal x y
  -- included in Obs: lws;coe
  int-ww : ( po-loc src ⨾ co src ) x y → Internal x y
  -- included in Obs: [R];pol;fre
  int-wr : ( po-loc src ⨾ fr src ) x y → Internal x y

-- like `Coh`, but `rf`, `fr`, and `co` are external
data Cohₘ (x y : EventTCG) : Set where
  coh-po-loc : po-loc src x y → Cohₘ x y
  coh-rfe    : rfe src x y → Cohₘ x y
  coh-fre    : fre src x y → Cohₘ x y
  coh-coe    : coe src x y → Cohₘ x y

-- Ordered Before (immediate). A subset of Arm's Ordered-Before, defined for TCG
data TCGObᵢ (x y : EventTCG) : Set where
  tob-coe : coe src x y → TCGObᵢ x y
  tob-rfe : rfe src x y → TCGObᵢ x y
  tob-fre : fre src x y → TCGObᵢ x y
  tob-lws : (po-loc src ⨾ ⦗ EvW ⦘) x y → TCGObᵢ x y
  tob-por : (⦗ EvR ⦘ ⨾ po-loc src ⨾ fre src) x y → TCGObᵢ x y

TCGOb = TransClosure TCGObᵢ
Coh⁺ = TransClosure (Coh src-mex)
Cohₘ⁺ = TransClosure Cohₘ

InternalCycle = ∃[ t ] Internal t t
ExternalCycle = ∃[ t ] TCGOb t t

poloc-trans : Transitive (po-loc src)
poloc-trans {x} {y} {z} (po[xy] , xy-sloc) (po[yz] , yz-sloc) =
  po-trans src-wf po[xy] po[yz] , trans-same-loc xy-sloc yz-sloc

rfˡ-w : {x y : EventTCG} → rf src x y → EvW x
rfˡ-w = ×₂-applyˡ (rf-w×r src-wf)

rfʳ-r : {x y : EventTCG} → rf src x y → EvR y
rfʳ-r = ×₂-applyʳ (rf-w×r src-wf)

coˡ-w : {x y : EventTCG} → co src x y → EvW x
coˡ-w = ×₂-applyˡ (co-w×w src-wf)

frˡ-r : {x y : EventTCG} → fr src x y → EvR x
frˡ-r = ×₂-applyˡ (fr-r×w src-wf)

frʳ-w : {x y : EventTCG} → fr src x y → EvW y
frʳ-w = ×₂-applyʳ (fr-r×w src-wf)

-- | Rotate a coherence chain such that it starts at a W event
coh⁺-start : {x : EventTCG} → Coh⁺ x x → ∃[ y ] EvW y × Coh⁺ y y
coh⁺-start [ coh[xx] ] = ⊥-elim (coh-irreflexive refl coh[xx])
coh⁺-start {x} (coh-po-loc pl[xy] ∷ coh⁺[yx]) = step pl[xy] coh⁺[yx]
  where
  -- Keep joining `po-loc`s, until we encounter something else
  step : {y : EventTCG} → po-loc src x y → Coh⁺ y x → ∃[ z ] EvW z × Coh⁺ z z
  step pl[xy] [ coh-po-loc pl[yx] ] =
    let po[xx] = po-trans src-wf (proj₁ pl[xy]) (proj₁ pl[yx])
    in ⊥-elim (po-irreflexive src-wf refl po[xx])
  step pl[xy] [ coh-rf rf[yx] ] = _ , rfˡ-w rf[yx] , coh-rf rf[yx] ∷ [ coh-po-loc pl[xy] ]
  step pl[xy] [ coh-fr fr[yx] ] = _ , frʳ-w fr[yx] , coh-po-loc pl[xy] ∷ [ coh-fr fr[yx] ]
  step pl[xy] [ coh-co co[yx] ] = _ , coˡ-w co[yx] , coh-co co[yx] ∷ [ coh-po-loc pl[xy] ]
  step pl[xy] (coh-po-loc pl[yz] ∷ coh⁺[zx]) = step (poloc-trans pl[xy] pl[yz]) coh⁺[zx]
  step pl[xy] (coh-rf rf[yz] ∷ coh⁺[zx]) =
    _ , rfˡ-w rf[yz] , coh-rf rf[yz] ∷ (coh⁺[zx] ∷ʳ coh-po-loc pl[xy])
  step pl[xy] (coh-fr fr[yz] ∷ coh⁺[zx]) =
    _ , frʳ-w fr[yz] , ((coh⁺[zx] ∷ʳ coh-po-loc pl[xy]) ∷ʳ coh-fr fr[yz])
  step pl[xy] (coh-co co[yz] ∷ coh⁺[zx]) =
    _ , coˡ-w co[yz] , coh-co co[yz] ∷ (coh⁺[zx] ∷ʳ coh-po-loc pl[xy])
coh⁺-start coh⁺[xx]@(coh-rf rf[xy] ∷ _) = _ , rfˡ-w rf[xy] , coh⁺[xx]
coh⁺-start (coh-fr fr[xy] ∷ coh⁺[yx])   = _ , frʳ-w fr[xy] , (coh⁺[yx] ∷ʳ coh-fr fr[xy])
coh⁺-start coh⁺[xx]@(coh-co co[xy] ∷ _) = _ , coˡ-w co[xy] , coh⁺[xx]

-- enables `do`-notation
_>>=_ : {A B C : Set} → A ⊎ C → ( A → B ⊎ C ) → B ⊎ C
inj₁ x >>= f = f x
inj₂ y >>= f = inj₂ y

coh-ext : {x y : EventTCG} → Coh src-mex x y → Cohₘ x y ⊎ InternalCycle
coh-ext (coh-po-loc pl[xy]) = inj₁ (coh-po-loc pl[xy])
coh-ext {x} {y} (coh-rf rf[xy]) with int⊎ext src-wf x y
... | inj₁ (opt₁ po[xy]) = inj₁ (coh-po-loc (po[xy] , ⊆₂-apply (rf-sloc src-wf) rf[xy]))
... | inj₁ (opt₂ po[yx]) =
  inj₂ (_ , int-rw ((po[yx] , sym-same-loc (⊆₂-apply (rf-sloc src-wf) rf[xy])) ⨾[ _ ]⨾ rf[xy]))
... | inj₁ (opf₃ x≡y) = ⊥-elim (rf-irreflexive src-wf x≡y rf[xy])
... | inj₂ ext-xy = inj₁ (coh-rfe (rf[xy] , ext-xy))
coh-ext {x} {y} (coh-fr fr[xy]) with int⊎ext src-wf x y
... | inj₁ (opt₁ po[xy]) =
  inj₁ (coh-po-loc (po[xy] , ⊆₂-apply (fr-sloc src-wf) fr[xy]))
... | inj₁ (opt₂ po[yx]) =
  inj₂ (_ , int-wr ((po[yx] , sym-same-loc (⊆₂-apply (fr-sloc src-wf) fr[xy])) ⨾[ _ ]⨾ fr[xy]))
... | inj₁ (opf₃ x≡y) = ⊥-elim (fr-irreflexive src-wf x≡y fr[xy])
... | inj₂ ext-xy = inj₁ (coh-fre (fr[xy] , ext-xy))
coh-ext {x} {y} (coh-co co[xy]) with int⊎ext src-wf x y
... | inj₁ (opt₁ po[xy]) = inj₁ (coh-po-loc (po[xy] , ⊆₂-apply (co-sloc src-wf) co[xy]))
... | inj₁ (opt₂ po[yx]) =
  inj₂ (_ , int-ww ((po[yx] , sym-same-loc (⊆₂-apply (co-sloc src-wf) co[xy])) ⨾[ _ ]⨾ co[xy]))
... | inj₁ (opf₃ x≡y) = ⊥-elim (co-irreflexive src-wf x≡y co[xy])
... | inj₂ ext-xy = inj₁ (coh-coe (co[xy] , ext-xy))

coh⁺ext : {x y : EventTCG} → Coh⁺ x y → Cohₘ⁺ x y ⊎ InternalCycle
coh⁺ext [ coh[xy] ] = map₁ [_] (coh-ext coh[xy])
coh⁺ext ( coh[xz] ∷ coh⁺[zy] ) =
  do
    cohₘ[xz]  ← coh-ext coh[xz]
    cohₘ⁺[zy] ← coh⁺ext coh⁺[zy]
    inj₁ (cohₘ[xz] ∷ cohₘ⁺[zy])

-- |
-- This does not *generally* produce `coe`. As init events are not external
chain-pol-fre : {x y z : EventTCG}
  → EvW x → po-loc src x y → fre src y z → co src x z ⊎ InternalCycle
chain-pol-fre {x} x-w pl[xy] fre[yz]@(rf⁻¹[yv] ⨾[ v ]⨾ co[vz] , ¬po[yz]) =
  let v-w = coˡ-w co[vz]
      xy-sloc = proj₂ pl[xy]
      yv-sloc = sym-same-loc (⊆₂-apply (rf-sloc src-wf) rf⁻¹[yv])
      xv-sloc = trans-same-loc xy-sloc yv-sloc
      x-has-loc = w-has-loc x-w
      v-has-loc = subst-sloc xv-sloc x-has-loc
      x∈src = poˡ∈ex src-wf (proj₁ pl[xy])
      v∈src = coˡ∈ex src-wf co[vz]
      x-pred : WithPred (EvW ∩₁ HasLoc _ ∩₁ events src)
      x-pred = with-pred x (x-w , x-has-loc , x∈src)
      v-pred : WithPred (EvW ∩₁ HasLoc _ ∩₁ events src)
      v-pred = with-pred v (v-w , v-has-loc , v∈src)
  in
  case co-tri src-wf _ x-pred v-pred of
  λ{ (tri< co[xv] _ _) →
       inj₁ (co-trans src-wf co[xv] co[vz])
   ; (tri≈ _ with-x≡v _) →
       let x≡v = with-pred-≡ with-x≡v
       in inj₁ (subst-rel (co src) (≡-sym x≡v) refl co[vz])
   ; (tri> _ _ co[vx]) →
       let fr[yx] = rf⁻¹[yv] ⨾[ _ ]⨾ co[vx]
       in opf₂ (_ , int-wr (pl[xy] ⨾[ _ ]⨾ fr[yx]))
   }

co-ext⊎pol : {x y : Event}
  → co src x y
  → ((coe src ∪₂ po-loc src) x y) ⊎ InternalCycle
co-ext⊎pol {x} {y} co[xy] with int⊎ext src-wf x y
... | opt₁ (opt₁ po[xy]) =
  opt₁ (opf₂ (po[xy] , ⊆₂-apply (co-sloc src-wf) co[xy]))
... | opt₁ (opt₂ po[yx]) =
  let pl[yx] = po[yx] , sym-same-loc (⊆₂-apply (co-sloc src-wf) co[xy])
  in opf₂ (_ , int-ww (pl[yx] ⨾[ _ ]⨾ co[xy]))
... | opt₁ (opf₃ x≡y) = ⊥-elim (co-irreflexive src-wf x≡y co[xy])
... | opf₂ ext-xy = opt₁ (opt₁ (co[xy] , ext-xy))

conv : {x y : EventTCG} → EvRW x → EvW y → Cohₘ⁺ x y → TCGOb x y ⊎ InternalCycle
conv x-rw y-w [ coh-po-loc pl[xy] ] = inj₁ [ tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , y-w)) ]
conv x-rw y-w [ coh-rfe rfe[xy] ] = inj₁ [ tob-rfe rfe[xy] ]
conv x-rw y-w [ coh-fre fre[xy] ] = inj₁ [ tob-fre fre[xy] ]
conv x-rw y-w [ coh-coe coe[xy] ] = inj₁ [ tob-coe coe[xy] ]
conv x-rw y-w (coh-po-loc pl[xz] ∷ coh⁺[zy]) = conv-pl x-rw y-w pl[xz] coh⁺[zy]
  where
  conv-pl : {x y z : EventTCG} → EvRW x → EvW z → po-loc src x y → Cohₘ⁺ y z → TCGOb x z ⊎ InternalCycle
  conv-pl x-rw z-w pl[xy] [ coh-po-loc pl[yz] ] =
    opt₁ [ tob-lws (poloc-trans pl[xy] pl[yz] ⨾[ _ ]⨾ (refl , z-w)) ]
  conv-pl x-rw z-w pl[xy] [ coh-rfe rfe[yz] ] = ⊥-elim (disjoint-r/w _ (rfʳ-r (proj₁ rfe[yz]) , z-w))
  conv-pl x-rw z-w pl[xy] [ coh-fre fre[yz] ] with rw/rw x-rw
  ... | inj₁ x-r = inj₁ [ tob-por ((refl , x-r) ⨾[ _ ]⨾ pl[xy] ⨾[ _ ]⨾ fre[yz]) ]
  ... | inj₂ x-w =
    do
      co[xz] ← chain-pol-fre x-w pl[xy] fre[yz]
      coe⊎pol ← co-ext⊎pol co[xz]
      case coe⊎pol of
        (λ{ (inj₁ coe[xz]) → inj₁ [ tob-coe coe[xz] ]
          ; (inj₂ pl[xz])  → inj₁ [ tob-lws (pl[xz] ⨾[ _ ]⨾ (refl , z-w)) ]
          })
  conv-pl x-rw z-w pl[xy] [ coh-coe coe[yz] ] =
    let y-w = coˡ-w (proj₁ coe[yz])
    in opt₁ (tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , y-w)) ∷ [ tob-coe coe[yz] ])
  conv-pl x-rw z-w pl[xy] (coh-po-loc pl[yv] ∷ coh⁺[vz]) =
    conv-pl x-rw z-w (poloc-trans pl[xy] pl[yv]) coh⁺[vz]
  conv-pl {x} {y} {z} x-rw z-w pl[xy] (coh-rfe rfe[yv] ∷ coh⁺[vz]) =
    let y-w = ×₂-applyˡ (rf-w×r src-wf) (proj₁ rfe[yv])
        v-rw = r⇒rw (×₂-applyʳ (rf-w×r src-wf) (proj₁ rfe[yv]))
        obᵢ[xy] = tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , y-w))
    in
    map₁
      (λ ob[vz] → obᵢ[xy] ∷ tob-rfe rfe[yv] ∷ ob[vz])
      (conv v-rw z-w coh⁺[vz])
  -- this is the trickiest case. we have either:
  -- * `[R];pl;fre` - which is `tob-por`
  -- * `[W];pl;coe` - which is either `tob-coe`, or is `[W];pl` which continues,
  --                  or becomes an internal cycle. (the continuing case should be
  --                  impossible, but is an artifact of our representation of init
  --                  events)
  conv-pl x-rw z-w pl[xy] (coh-fre fre[yv] ∷ coh⁺[vz]) with rw/rw x-rw
  ... | inj₁ x-r =
    let ob[xv] = tob-por ((refl , x-r) ⨾[ _ ]⨾ pl[xy] ⨾[ _ ]⨾ fre[yv])
        v-rw = w⇒rw (frʳ-w (proj₁ fre[yv]))
    in map₁ (ob[xv] ∷_) (conv v-rw z-w coh⁺[vz])
  ... | inj₂ x-w =
    do
      co[xv] ← chain-pol-fre x-w pl[xy] fre[yv]
      coe⊎pol ← co-ext⊎pol co[xv]
      let v-rw = w⇒rw (frʳ-w (proj₁ fre[yv]))
      case coe⊎pol of
        λ{ (inj₁ coe[xv]) → map₁ (tob-coe coe[xv] ∷_) (conv v-rw z-w coh⁺[vz])
         ; (inj₂ pol[xv]) → conv-pl x-rw z-w pol[xv] coh⁺[vz]
         }
  conv-pl x-rw z-w pl[xy] (coh-coe coe[yv] ∷ coh⁺[vz]) =
    let y-w = ×₂-applyˡ (co-w×w src-wf) (proj₁ coe[yv])
        v-rw = w⇒rw (×₂-applyʳ (co-w×w src-wf) (proj₁ coe[yv]))
    in
    map₁
      (λ ob[vz] → tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , y-w)) ∷ tob-coe coe[yv] ∷ ob[vz])
      (conv v-rw z-w coh⁺[vz])
conv x-rw y-w (coh-rfe rfe[xz] ∷ coh⁺[zy]) =
  let z-rw = r⇒rw (rfʳ-r (proj₁ rfe[xz]))
  in map₁ (tob-rfe rfe[xz] ∷_) (conv z-rw y-w coh⁺[zy])
conv x-rw y-w (coh-fre fre[xz] ∷ coh⁺[zy]) =
  let z-rw = w⇒rw (frʳ-w (proj₁ fre[xz]))
  in map₁ (tob-fre fre[xz] ∷_) (conv z-rw y-w coh⁺[zy])
conv x-rw y-w (coh-coe coe[xz] ∷ coh⁺[zy]) =
  let z-rw = w⇒rw (×₂-applyʳ (co-w×w src-wf) (proj₁ coe[xz]))
  in map₁ (tob-coe coe[xz] ∷_) (conv z-rw y-w coh⁺[zy])

coh⁺→tob : {x : EventTCG} → Coh⁺ x x → ExternalCycle ⊎ InternalCycle
coh⁺→tob coh⁺[xx] =
  do
    let (y , y-w , coh⁺[yy]) = coh⁺-start coh⁺[xx]
    cohₘ⁺[yy] ← coh⁺ext coh⁺[yy]
    map₁ (y ,_) (conv (w⇒rw y-w) y-w cohₘ⁺[yy])

src-ax-coherence : Acyclic _≡_ ( Coh src-mex )
src-ax-coherence refl coh⁺[xx] with coh⁺→tob coh⁺[xx]
... | inj₁ (_ , ob[yy]) =
  let y∈src = ⁺-lift-predˡ tobˡ∈src ob[yy]
  in ax-external dst-consistent refl (ob[⇒] y∈src y∈src ob[yy])
  where
  open Armv8Execution dst-a8
  open MixedExecution mix
  
  obᵢ[⇒] : Rel[⇒] TCGObᵢ Obi
  obᵢ[⇒] x∈src y∈src (tob-coe coe[xy]) =
    let (co[xy]ᵗ , xy-ext) = coe[⇒] x∈src y∈src coe[xy]
        y∈dst = coʳ∈ex dst-wf co[xy]ᵗ
        si[yy] = si-refl {with-pred _ y∈dst}
    in obi-obs (obs-cae (ca-co co[xy]ᵗ , xy-ext) ⨾[ _ ]⨾ si[yy])
  obᵢ[⇒] x∈src y∈src (tob-rfe rfe[xy]) =
    let (rf[xy]ᵗ , xy-ext) = rfe[⇒] x∈src y∈src rfe[xy]
        y∈dst = rfʳ∈ex dst-wf rf[xy]ᵗ
        si[yy] = si-refl {with-pred _ y∈dst}
    in obi-obs (obs-rfe (rf[xy]ᵗ , xy-ext) ⨾[ _ ]⨾ si[yy])
  obᵢ[⇒] x∈src y∈src (tob-fre fre[xy]) =
    let (fr[xy]ᵗ , xy-ext) = fre[⇒] x∈src y∈src fre[xy]
        y∈dst = frʳ∈ex dst-wf fr[xy]ᵗ
        si[yy] = si-refl {with-pred _ y∈dst}
    in obi-obs (obs-cae (ca-fr fr[xy]ᵗ , xy-ext) ⨾[ _ ]⨾ si[yy])
  obᵢ[⇒] x∈src y∈src (tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , y-w))) =
    let pl[xy]ᵗ = po-loc[⇒] x∈src y∈src pl[xy]
        y∈dst = events[⇒] y∈src
        si[yy] = si-refl {with-pred _ y∈dst}
    in obi-lob [ lobi-lws (pl[xy]ᵗ ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w) ⨾[ _ ]⨾ si[yy]) ]
  obᵢ[⇒] x∈src y∈src (tob-por ((refl , x-r) ⨾[ _ ]⨾ pl[xz] ⨾[ _ ]⨾ fre[zy])) =
    let xᵗ-r = R[⇒] x∈src x-r
        z∈src = poʳ∈src (proj₁ pl[xz])
        pl[xz]ᵗ = po-loc[⇒] x∈src z∈src pl[xz]
        y∈dst = events[⇒] y∈src
        fre[zy]ᵗ = fre[⇒] z∈src y∈src fre[zy]
        si[yy] = si-refl {with-pred _ y∈dst}
    in obi-fre ((refl , xᵗ-r) ⨾[ _ ]⨾ pl[xz]ᵗ ⨾[ _ ]⨾ fre[zy]ᵗ ⨾[ _ ]⨾ si[yy])

  tobˡ∈src : {x y : EventTCG} → TCGObᵢ x y → x ∈ events src
  tobˡ∈src (tob-coe coe[xy]) = coˡ∈src (proj₁ coe[xy])
  tobˡ∈src (tob-rfe rfe[xy]) = rfˡ∈src (proj₁ rfe[xy])
  tobˡ∈src (tob-fre fre[xy]) = frˡ∈src (proj₁ fre[xy])
  tobˡ∈src (tob-lws (pl[xy] ⨾[ _ ]⨾ (refl , _))) = poˡ∈src (proj₁ pl[xy])
  tobˡ∈src (tob-por ((refl , _) ⨾[ _ ]⨾ pl[xz] ⨾[ _ ]⨾ fre[zy])) = poˡ∈src (proj₁ pl[xz])

  ob[⇒] : Rel[⇒] TCGOb Ob
  ob[⇒] = ⁺[⇒]ˡ tobˡ∈src obᵢ[⇒]
... | inj₂ (_ , internal[yy]) = internal-⊥ internal[yy]
  where
  internal-⊥ : {x : EventTCG} → Internal x x → ⊥
  internal-⊥ {x} (int-rw (pl[xy] ⨾[ y ]⨾ rf[yx])) =
    let x∈src = poˡ∈src (proj₁ pl[xy])
        y∈src = rfˡ∈src rf[yx]
        xᵗ-r = R[⇒] x∈src (rfʳ-r rf[yx])
        yᵗ-w = W[⇒] y∈src (rfˡ-w rf[yx])
        pl[xy]ᵗ = po-loc[⇒] x∈src y∈src pl[xy]
        rfi[yx]ᵗ = rfi[⇒] y∈src x∈src (rf[yx] , opt₂ (proj₁ pl[xy]))
    in
    ax-internal-rw dst-consistent refl
      ((refl , xᵗ-r) ⨾[ _ ]⨾ inj₁ pl[xy]ᵗ ⨾[ _ ]⨾ (refl , yᵗ-w) ⨾[ _ ]⨾ rfi[yx]ᵗ ⨾[ _ ]⨾ (refl , xᵗ-r))
  internal-⊥ (int-ww (pl[xy] ⨾[ _ ]⨾ co[yx])) =
    let x∈src = poˡ∈src (proj₁ pl[xy])
        y∈src = coˡ∈src co[yx]
        xᵗ-w = W[⇒] x∈src (×₂-applyʳ (co-w×w src-wf) co[yx])
        yᵗ-w = W[⇒] y∈src (coˡ-w co[yx])
        pl[xy]ᵗ = po-loc[⇒] x∈src y∈src pl[xy]
        co[yx]ᵗ = co[⇒] y∈src x∈src co[yx]
    in
    ax-internal-ww dst-consistent refl
      ((refl , xᵗ-w) ⨾[ _ ]⨾ pl[xy]ᵗ ⨾[ _ ]⨾ (refl , yᵗ-w) ⨾[ _ ]⨾ ca-co co[yx]ᵗ ⨾[ _ ]⨾ (refl , xᵗ-w))
  internal-⊥ (int-wr (pl[xy] ⨾[ _ ]⨾ fr[yx])) =
    let x∈src = poˡ∈src (proj₁ pl[xy])
        y∈src = frˡ∈src fr[yx]
        xᵗ-w = W[⇒] x∈src (×₂-applyʳ (fr-r×w src-wf) fr[yx])
        yᵗ-r = R[⇒] y∈src (frˡ-r fr[yx])
        pl[xy]ᵗ = po-loc[⇒] x∈src y∈src pl[xy]
        fr[yx]ᵗ = fr[⇒] y∈src x∈src fr[yx]
    in
    ax-internal-wr dst-consistent refl
      ((refl , xᵗ-w) ⨾[ _ ]⨾ pl[xy]ᵗ ⨾[ _ ]⨾ (refl , yᵗ-r) ⨾[ _ ]⨾ ca-fr fr[yx]ᵗ ⨾[ _ ]⨾ (refl , xᵗ-w))


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

-- ## Helpers


-- ## Proof

src-ax-global-ord : Irreflexive _≡_ (ghb src-mex)
src-ax-global-ord refl ghb[xx] =
  let x∈src = ⁺-lift-predˡ ghbiˡ∈ex ghb[xx]
  in ax-external dst-consistent refl (⁺[⇒]ˡ ghbiˡ∈ex ghbi[⇒]obi x∈src x∈src ghb[xx])
  where
  ord[⇒]obi : Rel[⇒] (Ord src-mex) Obi
  ord[⇒]obi x∈src y∈src (ord-init ((refl , x-init) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) =
    obi-lob ([ lobi-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]) ])
  -- RR
  ord[⇒]obi x∈src y∈src (ord-rr ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RW
  ord[⇒]obi x∈src y∈src (ord-rw ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RM
  ord[⇒]obi x∈src y∈src (ord-rm ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- WR
  ord[⇒]obi x∈src y∈src (ord-wr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- WW
  ord[⇒]obi x∈src y∈src (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fst ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fww[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w))) ])
  -- WM
  ord[⇒]obi x∈src y∈src (ord-wm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MR
  ord[⇒]obi x∈src y∈src (ord-mr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MW
  ord[⇒]obi x∈src y∈src (ord-mw ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MM
  ord[⇒]obi x∈src y∈src (ord-mm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-rmw-codom ((refl , x∈rmwʳ@(z , rmw[zx])) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) =
    let z∈src = rmwˡ∈src rmw[zx]
    in obi-lob [ lobi-bob (bob-amo ((refl , ev[⇒] z∈src , rmw[⇒]amo-al z∈src x∈src rmw[zx]) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]
  ord[⇒]obi x∈src y∈src (ord-w ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₜ))) =
    obi-lob [ lobi-bob (bob-rel (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒]L y∈src y-wₜ))) ]
  ord[⇒]obi {x} x∈src y∈src (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) =
    obi-lob [ lobi-bob (bob-acq ((refl , inj₁ (Rₜ[⇒]A x∈src x-rₜ)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]

  ghbi[⇒]obi : Rel[⇒] (Ghbi src-mex) Obi
  ghbi[⇒]obi x∈src y∈src (ghbi-ord ord[xy]) = ord[⇒]obi x∈src y∈src ord[xy]
  ghbi[⇒]obi x∈src y∈src (ghbi-rfe (rfe[xz] ⨾[ z ]⨾ si[zy])) =
    let z∈src = rfʳ∈src (proj₁ rfe[xz])
        obs[xy] = obs-rfe (rfe[⇒] x∈src z∈src rfe[xz])
    in obi-obs (obs[xy] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy])
  ghbi[⇒]obi x∈src y∈src (ghbi-coe ((co[xz] , ext-xz) ⨾[ _ ]⨾ si[zy])) =
    let z∈src = coʳ∈src co[xz]
        extᵗ-xz = ext[⇒] x∈src z∈src ext-xz
        obs[xz] = obs-cae (ca-co (co[⇒] x∈src z∈src co[xz]) , extᵗ-xz)
    in obi-obs (obs[xz] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy])
  ghbi[⇒]obi x∈src y∈src (ghbi-fre ((fr[xz] , ext-xz) ⨾[ _ ]⨾ si[zy])) =
    let z∈src = frʳ∈src fr[xz]
        extᵗ-xz = ext[⇒] x∈src z∈src ext-xz
        obs[xz] = obs-cae (ca-fr (fr[⇒] x∈src z∈src fr[xz]) , extᵗ-xz)
    in obi-obs (obs[xz] ⨾[ _ ]⨾ si[⇒] z∈src y∈src si[zy])


-- # Result

src-consistent : IsTCGConsistent src-mex
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
