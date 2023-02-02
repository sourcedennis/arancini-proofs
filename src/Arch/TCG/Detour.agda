{-# OPTIONS --safe #-}

open import Arch.TCG using (arch-TCG)
open import Burrow.Template.Arch as Π


-- | A detour is an alternative path through an execution, which satisfies different desired properties.
-- This module defines a detour for TCG's ghb-relation. The detour guarantees that individual relations
-- within the cycle only go through R/W events; Whereas the original path could go between fences as well.
module Arch.TCG.Detour (ex : Execution {arch-TCG}) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_; _∷ʳ_)
-- Local library imports
open import Dodo.Unary
open import Dodo.Binary
open Π.Ev arch-TCG
open Π.Defs ex
-- Local imports
open import Helpers
open import Arch.TCG as TCG

open TCG.Relations ex


--
-- This module contains the following public components:
-- * OrdAlt - alternative definition of `Ord`
-- * GhbiAlt - alternative definition of `Ghbi`
-- * GhbiAlt⁺⇒Ghbi⁺ - converts back to the original ghb definition
-- * detour - converts from a `Ghbi` cycle to a `GhbiAlt` cycle
--

-- | This is an alternative definition of `Ord` (in `Arch.TCG`).
--
-- The following changes are included:
-- * The `SC` fence rules (`po;SC` and `SC;po`) are combined into a single rule
--   (`po;SC;po`)
-- * All edges are guaranteed to go between two R/W events
-- * All ACQ / REL fences are removed (they do nothing anyway)
data OrdAlt (x y : Event) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y
  
  ord-rr        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → OrdAlt x y
  ord-rw        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → OrdAlt x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po ⨾ ⦗ EvFₜ RM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y
  
  ord-wr        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → OrdAlt x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → OrdAlt x y
  ord-wm        : ( ⦗ EvW ⦘  ⨾ po ⨾ ⦗ EvFₜ WM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y
  
  ord-mr        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MR ⦘ ⨾ po ⨾ ⦗ EvR ⦘ )  x y → OrdAlt x y
  ord-mw        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MW ⦘ ⨾ po ⨾ ⦗ EvW ⦘ )  x y → OrdAlt x y
  ord-mm        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ MM ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y
  
  ord-sc        : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvFₜ SC ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y

  ord-rmw-dom   : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ dom rmw ⦘ )   x y → OrdAlt x y
  ord-rmw-codom : ( ⦗ codom rmw ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y

  ord-w         : ( ⦗ EvRW ⦘ ⨾ po ⨾ ⦗ EvWₜ trmw ⦘ ) x y → OrdAlt x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt x y


data GhbiAlt (x y : Event) : Set where
  ghbi-ord : OrdAlt x y → GhbiAlt x y
  ghbi-rfe : rfe x y    → GhbiAlt x y
  ghbi-coe : coe x y    → GhbiAlt x y
  ghbi-fre : fre x y    → GhbiAlt x y
  

OrdAlt⇒Ord⁺ : {x y : Event}
  → OrdAlt x y
    -----------------------
  → TransClosure Ord x y
OrdAlt⇒Ord⁺ (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-rr rr[xy]) = [ ord-rr rr[xy] ]
OrdAlt⇒Ord⁺ (ord-rw rw[xy]) = [ ord-rw rw[xy] ]
OrdAlt⇒Ord⁺ (ord-rm rm[xy]) = [ ord-rm rm[xy] ]
OrdAlt⇒Ord⁺ (ord-wr wr[xy]) = [ ord-wr wr[xy] ]
OrdAlt⇒Ord⁺ (ord-ww ww[xy]) = [ ord-ww ww[xy] ]
OrdAlt⇒Ord⁺ (ord-wm wm[xy]) = [ ord-wm wm[xy] ]
OrdAlt⇒Ord⁺ (ord-mr mr[xy]) = [ ord-mr mr[xy] ]
OrdAlt⇒Ord⁺ (ord-mw mw[xy]) = [ ord-mw mw[xy] ]
OrdAlt⇒Ord⁺ (ord-mm mm[xy]) = [ ord-mm mm[xy] ]
OrdAlt⇒Ord⁺ (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
  ord-sc₁ (po[xz] ⨾[ z ]⨾ (refl , z-sc)) ∷ [ ord-sc₂ ((refl , z-sc) ⨾[ z ]⨾ po[zy]) ]
OrdAlt⇒Ord⁺ (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  [ ord-rmw-dom (po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ)) ]
OrdAlt⇒Ord⁺ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-w ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-r))) =
  [ ord-w (po[xy] ⨾[ y ]⨾ (refl , y-r)) ]
OrdAlt⇒Ord⁺ (ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy]) ]


-- | Converts an alternative path to an original path
GhbiAlt⁺⇒Ghbi⁺ :
    {x y : Event}
  → TransClosure GhbiAlt x y
  → TransClosure Ghbi x y
GhbiAlt⁺⇒Ghbi⁺ ghbi-alt⁺[xy] =
  ⁺-join (⁺-map _ step ghbi-alt⁺[xy])
  where
  step : ∀ {x y : Event} → GhbiAlt x y → TransClosure Ghbi x y
  step (ghbi-ord ord[xy]) = ⁺-map _ ghbi-ord (OrdAlt⇒Ord⁺ ord[xy])
  step (ghbi-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  step (ghbi-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  step (ghbi-fre fre[xy]) = [ ghbi-fre fre[xy] ]


private
  -- Internal helper. Subsequent `Ord` elements are chained together, such that both ends
  -- of the chain contains R/W events
  --
  -- `ord⁺⇒alt` (below) traverses the fields of the `chain-ord` constructor to produce
  -- a sequence of `OrdAlt` elements.
  data Chain (x y : Event) : Set where
    chain-ord : EvRW x → EvRW y → TransClosure Ord x y → Chain x y
    chain-rfe : rfe x y → Chain x y
    chain-coe : coe x y → Chain x y
    chain-fre : fre x y → Chain x y


-- open import Burrow.WellFormed {arch-TCG} ex as Wf using (WellFormed)

module _ (wf : WellFormed ex) where

  open Π.WfDefs wf
  open TCG.Properties wf


  private
    f≢f : {t₁ t₂ : LabF} → t₁ ≢ t₂ → {x : Event} → EvFₜ t₁ x → EvFₜ t₂ x → ⊥
    f≢f t₁≢t₂ ev-f ev-f = t₁≢t₂ refl
    
    -- | Rotate the cycle such that it starts at a R/W event.
    --
    -- Note that every `ghb` cycle contains at least one R/W event, as every cycle passes through
    -- multiple threads. The only way to switch threads is through either of rfe, coe, or fre.
    -- Those relations all relate R/W events.
    rotate : {x : Event}
      → TransClosure Ghbi x x
      → ∃[ y ] TransClosure Ghbi y y × EvRW y
    rotate {x} [ ghbi[xx] ] = ⊥-elim (ghbi-irreflexive refl ghbi[xx])
    rotate {x} ghbi⁺[xx]@(ghbi-rfe rfe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ rfe-w×r rfe[xy])
    rotate {x} ghbi⁺[xx]@(ghbi-coe coe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ coe-w×w coe[xy])
    rotate {x} ghbi⁺[xx]@(ghbi-fre fre[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , r⇒rw (×₂-applyˡ fre-r×w fre[xy])
    rotate {x} (ghbi-ord ord[xy] ∷ ghbi⁺[yx]) = step [ ord[xy] ] ghbi⁺[yx]
      where
      step : {x y : Event}
        → TransClosure Ord x y → TransClosure Ghbi y x → ∃[ z ] TransClosure Ghbi z z × EvRW z
      step ord⁺[xy] [ ghbi-ord ord[yx] ] =
        let po[xx] = ord⁺⇒po (ord⁺[xy] ∷ʳ ord[yx])
        in ⊥-elim (po-irreflexive refl po[xx])
      step {x} {y} ord⁺[xy] [ ghbi-rfe rfe[yx]@(rf[yx] , _) ] =
        x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-rfe rfe[yx] ] , r⇒rw (×₂-applyʳ rf-w×r rf[yx])
      step {x} {y} ord⁺[xy] [ ghbi-coe coe[yx]@(co[yx] , _) ] = 
        x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-coe coe[yx] ] , w⇒rw (×₂-applyʳ co-w×w co[yx])
      step {x} {y} ord⁺[xy] [ ghbi-fre fre[yx]@(fr[yx] , _) ] = 
        x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-fre fre[yx] ] , w⇒rw (×₂-applyʳ fr-r×w fr[yx])
      step ord⁺[xy] (ghbi-ord ord[yw] ∷ ghbi⁺[wx]) =
        step (ord⁺[xy] ∷ʳ ord[yw]) ghbi⁺[wx]
      step {x} {y} ord⁺[xy] (ghbi-rfe rfe[yw]@(rf[yw] , _) ∷ ghbi⁺[wx]) =
        y , (ghbi-rfe rfe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ rf-w×r rf[yw])
      step {x} {y} ord⁺[xy] (ghbi-coe coe[yw]@(co[yw] , _) ∷ ghbi⁺[wx]) =
        y , (ghbi-coe coe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ co-w×w co[yw])
      step {x} {y} ord⁺[xy] (ghbi-fre fre[yw]@(fr[yw] , _) ∷ ghbi⁺[wx]) =
        y , (ghbi-fre fre[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , r⇒rw (×₂-applyˡ fr-r×w fr[yw])

    to-chain :
        {x y : Event}
      → EvRW x
      → EvRW y
      → TransClosure Ghbi x y
      → TransClosure Chain x y
    to-chain {x} {y} x-rw y-rw [ ghbi-ord ord[xy] ] = [ chain-ord x-rw y-rw [ ord[xy] ] ]
    to-chain {x} {y} x-rw y-rw [ ghbi-rfe rfe[xy] ] = [ chain-rfe rfe[xy] ]
    to-chain {x} {y} x-rw y-rw [ ghbi-coe coe[xy] ] = [ chain-coe coe[xy] ]
    to-chain {x} {y} x-rw y-rw [ ghbi-fre fre[xy] ] = [ chain-fre fre[xy] ]
    to-chain {x} {y} x-rw y-rw (ghbi-rfe rfe[xz] ∷ ghbi⁺[zy]) = chain-rfe rfe[xz] ∷ to-chain (r⇒rw (×₂-applyʳ rfe-w×r rfe[xz])) y-rw ghbi⁺[zy]
    to-chain {x} {y} x-rw y-rw (ghbi-coe coe[xz] ∷ ghbi⁺[zy]) = chain-coe coe[xz] ∷ to-chain (w⇒rw (×₂-applyʳ coe-w×w coe[xz])) y-rw ghbi⁺[zy]
    to-chain {x} {y} x-rw y-rw (ghbi-fre fre[xz] ∷ ghbi⁺[zy]) = chain-fre fre[xz] ∷ to-chain (w⇒rw (×₂-applyʳ fre-r×w fre[xz])) y-rw ghbi⁺[zy]
    to-chain {x} {y} x-rw y-rw (ghbi-ord ord[xz] ∷ ghbi⁺[zy]) = step [ ord[xz] ] ghbi⁺[zy]
      where
      -- | `ord⁺[xz]` is the accumulator. `step` performs structural recursion on the second (explicit) argument.
      step : {z : Event} → TransClosure Ord x z → TransClosure Ghbi z y → TransClosure Chain x y
      step ord⁺[xz] [ ghbi-ord ord[zy] ] = [ chain-ord x-rw y-rw ( ord⁺[xz] ∷ʳ ord[zy] ) ]
      step ord⁺[xz] [ ghbi-rfe rfe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ rfe-w×r rfe[zy])) ord⁺[xz] ∷ [ chain-rfe rfe[zy] ]
      step ord⁺[xz] [ ghbi-coe coe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ coe-w×w coe[zy])) ord⁺[xz] ∷ [ chain-coe coe[zy] ]
      step ord⁺[xz] [ ghbi-fre fre[zy] ] = chain-ord x-rw (r⇒rw (×₂-applyˡ fre-r×w fre[zy])) ord⁺[xz] ∷ [ chain-fre fre[zy] ]
      step ord⁺[xz] (ghbi-ord ord[zq] ∷ ghbi⁺[qy]) = step (ord⁺[xz] ∷ʳ ord[zq]) ghbi⁺[qy]
      step ord⁺[xz] (ghbi-rfe rfe[zq] ∷ ghbi⁺[qy]) =
        let (z-w , q-r) = ⊆₂-apply rfe-w×r rfe[zq]
        in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-rfe rfe[zq] ∷ to-chain (r⇒rw q-r) y-rw ghbi⁺[qy]
      step ord⁺[xz] (ghbi-coe coe[zq] ∷ ghbi⁺[qy]) =
        let (z-w , q-w) = ⊆₂-apply coe-w×w coe[zq]
        in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-coe coe[zq] ∷ to-chain (w⇒rw q-w) y-rw ghbi⁺[qy]
      step ord⁺[xz] (ghbi-fre fre[zq] ∷ ghbi⁺[qy]) =
        let (z-r , q-w) = ⊆₂-apply fre-r×w fre[zq]
        in chain-ord x-rw (r⇒rw z-r) ord⁺[xz] ∷ chain-fre fre[zq] ∷ to-chain (w⇒rw q-w) y-rw ghbi⁺[qy]

  ord⁺⇒alt :
      {x y : Event}
    → EvRW x
    → EvRW y
    → TransClosure Ord x y
    → TransClosure OrdAlt x y
  ord⁺⇒alt x-rw y-rw [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw [ ord-rr rr[xy] ] = [ ord-rr rr[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-rw rw[xy] ] = [ ord-rw rw[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-rm rm[xy] ] = [ ord-rm rm[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-wr wr[xy] ] = [ ord-wr wr[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-ww ww[xy] ] = [ ord-ww ww[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-wm wm[xy] ] = [ ord-wm wm[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-mr mr[xy] ] = [ ord-mr mr[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-mw mw[xy] ] = [ ord-mw mw[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-mm mm[xy] ] = [ ord-mm mm[xy] ]
  ord⁺⇒alt x-rw y-rw [ ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] =
    [ ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ]
  ord⁺⇒alt x-rw y-rw [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw [ ord-w (po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ] =
    [ ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ]
  ord⁺⇒alt x-rw y-rw [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po ord⁺[zy]
        po[xy] = po-trans po[xz] po[zy]
    in [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt {ex} x-rw y-rw (ord-ww ww[xz] ∷ ord⁺[zy]) =
    ord-ww ww[xz] ∷ ord⁺⇒alt (w⇒rw (ord-predʳ ww[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} x-rw y-rw (ord-rm rm[xz] ∷ ord⁺[zy]) =
    ord-rm rm[xz] ∷ ord⁺⇒alt (ord-predʳ rm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-sc₁ (po[xz] ⨾[ _ ]⨾ (refl , z-sc)) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po ord⁺[zy]
    in [ ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw (ord-rmw-dom (po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ)) ∷ ord⁺[zy]) =
    ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ)) ∷ ord⁺⇒alt (rₜ⇒rw (rmwˡ-r z∈rmwˡ)) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po ord⁺[zy]
        po[xy] = po-trans po[xz] po[zy]
    in [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw (ord-w (po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺[zy]) =
    ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺⇒alt (wₜ⇒rw z-w) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po ord⁺[zy]
        po[xy] = po-trans po[xz] po[zy]
    in [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt x-rw y-rw [ ord-acq ((refl , ev-f) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/rw _ (ev-f , x-rw))
  ord⁺⇒alt x-rw y-rw [ ord-rel (po[xy] ⨾[ _ ]⨾ (refl , ev-f)) ] = ⊥-elim (disjoint-f/rw _ (ev-f , y-rw))
  -- Impossible cases
  ord⁺⇒alt x-rw y-rw [ ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , y-sc)) ] = ⊥-elim (disjoint-f/rw _ (fₜ⇒f y-sc , y-rw))
  ord⁺⇒alt x-rw y-rw [ ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/rw _ (fₜ⇒f x-sc , x-rw))
  ord⁺⇒alt x-rw y-rw (ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) = ⊥-elim (disjoint-f/rw _ (fₜ⇒f x-sc , x-rw))
  ord⁺⇒alt x-rw y-rw (ord-rr rr[xz] ∷ ord⁺[zy]) = ord-rr rr[xz] ∷ ord⁺⇒alt (r⇒rw (ord-predʳ rr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-rw rw[xz] ∷ ord⁺[zy]) = ord-rw rw[xz] ∷ ord⁺⇒alt (w⇒rw (ord-predʳ rw[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-wr wr[xz] ∷ ord⁺[zy]) = ord-wr wr[xz] ∷ ord⁺⇒alt (r⇒rw (ord-predʳ wr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-wm wm[xz] ∷ ord⁺[zy]) = ord-wm wm[xz] ∷ ord⁺⇒alt (ord-predʳ wm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-mr mr[xz] ∷ ord⁺[zy]) = ord-mr mr[xz] ∷ ord⁺⇒alt (r⇒rw (ord-predʳ mr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-mw mw[xz] ∷ ord⁺[zy]) = ord-mw mw[xz] ∷ ord⁺⇒alt (w⇒rw (ord-predʳ mw[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-mm mm[xz] ∷ ord⁺[zy]) = ord-mm mm[xz] ∷ ord⁺⇒alt (ord-predʳ mm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt x-rw y-rw (ord-acq ((refl , ev-f₌) ⨾[ _ ]⨾ po[xy]) ∷ ord⁺[zy]) = ⊥-elim (disjoint-f/rw _ (fₜ⇒f ev-f₌ , x-rw))
  ord⁺⇒alt {x} {y} x-rw y-rw (ord-rel (po[xz] ⨾[ _ ]⨾ (refl , ev-f₌)) ∷ ord⁺[zy]) = lemma po[xz] ev-f₌ ord⁺[zy]
    where
    -- Drop the REL fence
    lemma : ∀ {z : Event}
      → po x z
      → EvFₜ LabF.REL z
      → TransClosure Ord z y
        ----------------------------
      → TransClosure OrdAlt x y
    -- the REL fence is not needed, as the RMW-domain orders `x` with `y`
    lemma po[xz] z-f [ ord-rmw-dom (po[zy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] =
      [ ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po-trans po[xz] po[zy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ]
    -- the REL fence is not needed, as the RMW-write orders `x` with `y`
    lemma po[xz] z-f [ ord-w (po[zy] ⨾[ _ ]⨾ (refl , y-wₜ)) ] =
      [ ord-w ((refl , x-rw) ⨾[ _ ]⨾ po-trans po[xz] po[zy] ⨾[ _ ]⨾ (refl , y-wₜ)) ]
    -- Another REL fence. "Merge" them and drop them together
    lemma po[xz] z-f (ord-rel (po[zk] ⨾[ y ]⨾ (refl , ev-f)) ∷ ord⁺[ky]) =
      lemma (po-trans po[xz] po[zk]) ev-f ord⁺[ky]
    -- the REL fence is not needed, as the SC fence orders `x` with `y`
    lemma po[xz] z-f (ord-sc₁ (po[zk] ⨾[ _ ]⨾ (refl , ev-f)) ∷ ord⁺[ky]) =
      [ ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po-trans po[xz] po[zk] ⨾[ _ ]⨾ (refl , ev-f) ⨾[ _ ]⨾ ord⁺⇒po ord⁺[ky] ⨾[ _ ]⨾ (refl , y-rw)) ]
    -- the REL fence is not needed, as the RMW-domain orders `x` with `y`
    lemma po[xz] z-f (ord-rmw-dom (po[zk] ⨾[ _ ]⨾ (refl , k∈rmwˡ)) ∷ ord⁺[ky]) =
      let k-rw = rₜ⇒rw (rmwˡ-r k∈rmwˡ)
      in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po-trans po[xz] po[zk] ⨾[ _ ]⨾ (refl , k∈rmwˡ)) ∷ ord⁺⇒alt k-rw y-rw ord⁺[ky]
    -- the REL fence is not needed, as the RMW-write orders `x` with `y`
    lemma po[xz] z-f (ord-w (po[zk] ⨾[ _ ]⨾ (refl , k-wₜ)) ∷ ord⁺[ky]) =
      ord-w ((refl , x-rw) ⨾[ _ ]⨾ po-trans po[xz] po[zk] ⨾[ _ ]⨾ (refl , k-wₜ)) ∷ ord⁺⇒alt (wₜ⇒rw k-wₜ) y-rw ord⁺[ky]
    -- impossible cases
    lemma po[xz] z-f [ ord-init ((refl , z-init) ⨾[ _ ]⨾ po[zy]) ] = ⊥-elim (disjoint-f/init _ (fₜ⇒f z-f , z-init))
    lemma po[xz] z-f [ ord-rr rr[zy] ] = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rr[zy]))
    lemma po[xz] z-f [ ord-rw rw[zy] ] = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rw[zy]))
    lemma po[xz] z-f [ ord-rm rm[zy] ] = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rm[zy]))
    lemma po[xz] z-f [ ord-wr wr[zy] ] = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ wr[zy]))
    lemma po[xz] z-f [ ord-ww ww[zy] ] = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ ww[zy]))
    lemma po[xz] z-f [ ord-wm wm[zy] ] = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ wm[zy]))
    lemma po[xz] z-f [ ord-mr mr[zy] ] = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mr[zy]))
    lemma po[xz] z-f [ ord-mw mw[zy] ] = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mw[zy]))
    lemma po[xz] z-f [ ord-mm mm[zy] ] = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mm[zy]))
    lemma po[xz] z-f [ ord-acq ((refl , z-f₂) ⨾[ z ]⨾ po[zy]) ] = ⊥-elim (f≢f (λ ()) z-f z-f₂)
    lemma po[xz] z-f [ ord-rel (po[zy] ⨾[ y ]⨾ (refl , ev-f)) ] = ⊥-elim (disjoint-f/rw _ (ev-f , y-rw))
    lemma po[xz] z-f [ ord-sc₁ (po[zy] ⨾[ y ]⨾ (refl , ev-f)) ] = ⊥-elim (disjoint-f/rw _ (ev-f , y-rw))
    lemma po[xz] z-f [ ord-sc₂ ((refl , z-f₂) ⨾[ _ ]⨾ po[zy]) ] = ⊥-elim (f≢f (λ ()) z-f z-f₂)
    lemma po[xz] z-f [ ord-rmw-codom ((refl , z∈rmwʳ) ⨾[ _ ]⨾ po[zy]) ] = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , wₜ⇒w (rmwʳ-w z∈rmwʳ)))
    lemma po[xz] z-f [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , rₜ⇒r x-rₜ))
    lemma po[xz] z-f (ord-init ((refl , z-init) ⨾[ _ ]⨾ po[zk]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/init _ (fₜ⇒f z-f , z-init))
    lemma po[xz] z-f (ord-rr rr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rr[zk]))
    lemma po[xz] z-f (ord-rw rw[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rw[zk]))
    lemma po[xz] z-f (ord-rm rm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , ord-predˡ rm[zk]))
    lemma po[xz] z-f (ord-wr wr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ wr[zk]))
    lemma po[xz] z-f (ord-ww ww[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ ww[zk]))
    lemma po[xz] z-f (ord-wm wm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , ord-predˡ wm[zk]))
    lemma po[xz] z-f (ord-mr mr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mr[zk]))
    lemma po[xz] z-f (ord-mw mw[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mw[zk]))
    lemma po[xz] z-f (ord-mm mm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (fₜ⇒f z-f , ord-predˡ mm[zk]))
    lemma po[xz] z-f (ord-acq ((refl , z-f₂) ⨾[ z ]⨾ po[zk]) ∷ ord⁺[ky]) = ⊥-elim (f≢f (λ ()) z-f z-f₂)
    lemma po[xz] z-f (ord-sc₂ ((refl , z-f₂) ⨾[ _ ]⨾ po[zy]) ∷ ord⁺[ky]) = ⊥-elim (f≢f (λ ()) z-f z-f₂)
    lemma po[xz] z-f (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[zk]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (fₜ⇒f z-f , wₜ⇒w (rmwʳ-w x∈rmwʳ)))
    lemma po[xz] z-f (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (fₜ⇒f z-f , rₜ⇒r x-rₜ))
  
  chain⇒alt⁺ : {x y : Event} → Chain x y → TransClosure GhbiAlt x y
  chain⇒alt⁺ (chain-ord x-rw y-rw ord⁺[xy]) = ⁺-map _ ghbi-ord (ord⁺⇒alt x-rw y-rw ord⁺[xy])
  chain⇒alt⁺ (chain-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  chain⇒alt⁺ (chain-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  chain⇒alt⁺ (chain-fre fre[xy]) = [ ghbi-fre fre[xy] ]

  chain⁺⇒alt⁺ : {x y : Event}
    → TransClosure Chain x y → TransClosure GhbiAlt x y
  chain⁺⇒alt⁺ = ⇔₂-apply-⊇₂ ⁺-idem ∘ ⁺-map _ chain⇒alt⁺


  -- | Converts a `Ghbi` /cycle/ into an alternative `GhbiAlt` cycle, which
  -- contains only relations that go between read/write events.
  --
  -- Note that every ghbi-cycle goes between multiple threads. Moving to another thread
  -- always goes through rfe/coe/fre; which are all between read/write events.
  detour : {x : Event}
    → TransClosure Ghbi x x
    → ∃[ y ] TransClosure GhbiAlt y y
  detour {x} ghbi⁺[xx] = 
    let (y , ghbi⁺[yy] , y-rw) = rotate ghbi⁺[xx]
        chain⁺[yy] = to-chain y-rw y-rw ghbi⁺[yy]
    in y , chain⁺⇒alt⁺ chain⁺[yy]


  OrdAlt⇒po :
      {x y : Event}
    → OrdAlt x y
      -------------
    → po x y
  OrdAlt⇒po ord[xy] =
    let po⁺[xy] = ⁺-map (λ τ → τ) ord⇒po (OrdAlt⇒Ord⁺ ord[xy])
    in ⁺-join-trans po-trans po⁺[xy]

  OrdAlt-irreflexive : Irreflexive _≡_ OrdAlt
  OrdAlt-irreflexive refl = po-irreflexive refl ∘ OrdAlt⇒po

  GhbiAlt-irreflexive : Irreflexive _≡_ GhbiAlt
  GhbiAlt-irreflexive refl (ghbi-ord ord[xx]) = OrdAlt-irreflexive refl ord[xx]
  GhbiAlt-irreflexive refl (ghbi-rfe rfe[xx]) = rf-irreflexive refl (proj₁ rfe[xx])
  GhbiAlt-irreflexive refl (ghbi-coe coe[xx]) = co-irreflexive refl (proj₁ coe[xx])
  GhbiAlt-irreflexive refl (ghbi-fre fre[xx]) = fr-irreflexive refl (proj₁ fre[xx])


  -- # Helpers

  OrdAltˡ∈ex : OrdAlt ˡ∈ex
  OrdAltˡ∈ex = ⁺-lift-predˡ (poˡ∈ex ∘ ord⇒po) ∘ OrdAlt⇒Ord⁺

  GhbiAltˡ∈ex : GhbiAlt ˡ∈ex
  GhbiAltˡ∈ex (ghbi-ord ord[xy]) = OrdAltˡ∈ex ord[xy]
  GhbiAltˡ∈ex (ghbi-rfe rfe[xy]) = rfˡ∈ex (proj₁ rfe[xy])
  GhbiAltˡ∈ex (ghbi-coe coe[xy]) = coˡ∈ex (proj₁ coe[xy])
  GhbiAltˡ∈ex (ghbi-fre fre[xy]) = frˡ∈ex (proj₁ fre[xy])


  private
    ordfʳ+po :
        {P₁ P₂ : Pred₀ Event}
      → {m : LabF}
      → {x y z : Event}
      → ( ⦗ P₁ ⦘  ⨾ po ⨾ ⦗ EvFₜ m ⦘ ⨾ po ⨾ ⦗ P₂ ⦘ ) x y
      → po y z
      → P₂ z
        -----------------------------------------------------
      → ( ⦗ P₁ ⦘  ⨾ po ⨾ ⦗ EvFₜ m ⦘ ⨾ po ⨾ ⦗ P₂ ⦘ ) x z
    ordfʳ+po ((refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qy] ⨾[ _ ]⨾ (refl , y-p₂)) po[yz] z-p₂ =
      let po[qz] = po-trans po[qy] po[yz]
      in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , z-p₂)


  ordʳ+wᵣ :
      {x y z : Event}
    → OrdAlt x y
    → po y z
    → EvW y
    → EvW z
      -----------------------
    → TransClosure OrdAlt x z
  ordʳ+wᵣ (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) po[yz] y-w z-w =
    [ ord-init ((refl , x-init) ⨾[ _ ]⨾ po-trans po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-rw rw[xy]) po[yz] y-w z-w = [ ord-rw (ordfʳ+po rw[xy] po[yz] z-w) ]
  ordʳ+wᵣ (ord-rm rm[xy]) po[yz] y-w z-w = [ ord-rm (ordfʳ+po rm[xy] po[yz] (w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-ww ww[xy]) po[yz] y-w z-w = [ ord-ww (ordfʳ+po ww[xy] po[yz] z-w) ]
  ordʳ+wᵣ (ord-wm wm[xy]) po[yz] y-w z-w = [ ord-wm (ordfʳ+po wm[xy] po[yz] (w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-mw mw[xy]) po[yz] y-w z-w = [ ord-mw (ordfʳ+po mw[xy] po[yz] z-w) ]
  ordʳ+wᵣ (ord-mm mm[xy]) po[yz] y-w z-w = [ ord-mm (ordfʳ+po mm[xy] po[yz] (w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-sc sc[xy]) po[yz] y-w z-w = [ ord-sc (ordfʳ+po sc[xy] po[yz] (w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
    [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po-trans po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-w w[xy]@(_ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ (refl , y-wₐ))) po[yz] y-w z-w =
    let y∈ex = poˡ∈ex po[yz]
        y∈rmwʳ = ⇔₁-apply-⊇₁ rmw-w (y∈ex , y-wₐ)
    in ord-w w[xy] ∷ [ ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
  ordʳ+wᵣ (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
    [ ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po-trans po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
  -- impossible cases
  ordʳ+wᵣ (ord-rr rr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ rr[xy] , y-w))
  ordʳ+wᵣ (ord-wr wr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ wr[xy] , y-w))
  ordʳ+wᵣ (ord-mr mr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ mr[xy] , y-w))
  ordʳ+wᵣ (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) po[yz] y-w z-w =
    ⊥-elim (disjoint-r/w _ (rₜ⇒r (rmwˡ-r y∈rmwˡ) , y-w))

  private
    ordfˡ+po :
        {P₁ P₂ : Pred₀ Event}
      → {m : LabF}
      → {x y z : Event}
      → po x y
      → ( ⦗ P₁ ⦘  ⨾ po ⨾ ⦗ EvFₜ m ⦘ ⨾ po ⨾ ⦗ P₂ ⦘ ) y z
      → P₁ x
        -----------------------------------------------
      → ( ⦗ P₁ ⦘  ⨾ po ⨾ ⦗ EvFₜ m ⦘ ⨾ po ⨾ ⦗ P₂ ⦘ ) x z
    ordfˡ+po po[xy] ((refl , y-p₁) ⨾[ _ ]⨾ po[yq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)) x-p₁ =
      let po[xq] = po-trans po[xy] po[yq]
      in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)


  ordˡ+rᵣ :
      {x y z : Event}
    → po x y
    → OrdAlt y z
    → EvRᵣ y
    → EvRᵣ x
      -------------
    → OrdAlt x z
  ordˡ+rᵣ po[xy] (ord-rr rr[yz]) y-rᵣ x-rᵣ = ord-rr (ordfˡ+po po[xy] rr[yz] (rₜ⇒r x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-rw rw[yz]) y-rᵣ x-rᵣ = ord-rw (ordfˡ+po po[xy] rw[yz] (rₜ⇒r x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-rm rm[yz]) y-rᵣ x-rᵣ = ord-rm (ordfˡ+po po[xy] rm[yz] (rₜ⇒r x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-mr mr[yz]) y-rᵣ x-rᵣ = ord-mr (ordfˡ+po po[xy] mr[yz] (rₜ⇒rw x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-mw mw[yz]) y-rᵣ x-rᵣ = ord-mw (ordfˡ+po po[xy] mw[yz] (rₜ⇒rw x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-mm mm[yz]) y-rᵣ x-rᵣ = ord-mm (ordfˡ+po po[xy] mm[yz] (rₜ⇒rw x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-sc sc[yz]) y-rᵣ x-rᵣ = ord-sc (ordfˡ+po po[xy] sc[yz] (rₜ⇒rw x-rᵣ))
  ordˡ+rᵣ po[xy] (ord-rmw-dom ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))) y-rᵣ x-rᵣ =
    let po[xz] = po-trans po[xy] po[yz]
    in ord-rmw-dom ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))
  ordˡ+rᵣ po[xy] (ord-w ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-wₜ))) y-rᵣ x-rᵣ =
    let po[xz] = po-trans po[xy] po[yz]
    in ord-w ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-wₜ))
  -- impossible cases
  ordˡ+rᵣ po[xy] (ord-init ((refl , y-init) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
    ⊥-elim (disjoint-r/init _ (rₜ⇒r y-rᵣ , y-init))
  ordˡ+rᵣ {ex} po[xy] (ord-wr wr[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ wr[yz]))
  ordˡ+rᵣ {ex} po[xy] (ord-ww ww[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ ww[yz]))
  ordˡ+rᵣ {ex} po[xy] (ord-wm wm[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ wm[yz]))
  ordˡ+rᵣ po[xy] (ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
    ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , wₜ⇒w (rmwʳ-w y∈rmwʳ)))
  ordˡ+rᵣ po[xy] (ord-r ((refl , y-rₐ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
    ⊥-elim (disjoint-rₜ _ (y-rᵣ , y-rₐ))

  ghbi⇒po/sloc :
      {x y : Event}
    → GhbiAlt x y
    → (po ∪₂ SameLoc) x y
  ghbi⇒po/sloc (ghbi-ord ord[xy]) = inj₁ (OrdAlt⇒po ord[xy])
  ghbi⇒po/sloc (ghbi-rfe rfe[xy]) = inj₂ (⊆₂-apply rf-sloc (proj₁ rfe[xy]))
  ghbi⇒po/sloc (ghbi-coe coe[xy]) = inj₂ (⊆₂-apply co-sloc (proj₁ coe[xy]))
  ghbi⇒po/sloc (ghbi-fre fre[xy]) = inj₂ (⊆₂-apply fr-sloc (proj₁ fre[xy]))


  ghbi⇒coh :
      {x y : Event}
    → SameLoc x y
    → GhbiAlt x y
      -------------
    → Coh x y
  ghbi⇒coh xy-sloc (ghbi-ord ord[xy]) = coh-po-loc (OrdAlt⇒po ord[xy] , xy-sloc)
  ghbi⇒coh _       (ghbi-rfe rfe[xy]) = coh-rf (proj₁ rfe[xy])
  ghbi⇒coh _       (ghbi-coe coe[xy]) = coh-co (proj₁ coe[xy])
  ghbi⇒coh _       (ghbi-fre fre[xy]) = coh-fr (proj₁ fre[xy])


  -- | There exists no GHB cycle of length one
  ¬ghbi-cycle₁ :
      {x : Event}
    → GhbiAlt x x
    → ⊥
  ¬ghbi-cycle₁ = GhbiAlt-irreflexive refl


  -- | There exists no GHB cycle of length two
  ¬ghbi-cycle₂ :
      Acyclic _≡_ Coh
    → {x y : Event}
    → GhbiAlt x y → GhbiAlt y x
    → ⊥
  ¬ghbi-cycle₂ coh ghbi[xy] ghbi[yx] with ghbi⇒po/sloc ghbi[yx]
  ¬ghbi-cycle₂ coh (ghbi-ord ord[xy]) _ | inj₁ po[yx]  =
    po-irreflexive refl (po-trans (OrdAlt⇒po ord[xy]) po[yx])
  ¬ghbi-cycle₂ coh (ghbi-rfe rfe[xy]) _ | inj₁ po[yx]  =
    let yx-sloc = sym-same-loc (⊆₂-apply rf-sloc (proj₁ rfe[xy]))
    in coh refl (coh-rf (proj₁ rfe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
  ¬ghbi-cycle₂ coh (ghbi-coe coe[xy]) _ | inj₁ po[yx]  =
    let yx-sloc = sym-same-loc (⊆₂-apply co-sloc (proj₁ coe[xy]))
    in coh refl (coh-co (proj₁ coe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
  ¬ghbi-cycle₂ coh (ghbi-fre fre[xy]) _ | inj₁ po[yx]  =
    let yx-sloc = sym-same-loc (⊆₂-apply fr-sloc (proj₁ fre[xy]))
    in coh refl (coh-fr (proj₁ fre[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
  ¬ghbi-cycle₂ coh ghbi[xy]        ghbi[yx] | inj₂ yx-sloc =
    coh refl (ghbi⇒coh (sym-same-loc yx-sloc) ghbi[xy] ∷ [ ghbi⇒coh yx-sloc ghbi[yx] ])
