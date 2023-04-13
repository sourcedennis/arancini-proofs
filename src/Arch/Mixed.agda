{-# OPTIONS --safe #-}


-- | Mixed-size extension for regular `Execution`s
module Arch.Mixed where

-- stdlib imports
open import Relation.Binary.PropositionalEquality using (refl)
open import Function using (flip; _∘_)
open import Relation.Binary using (Reflexive; Transitive; Symmetric)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂) renaming ([_,_] to ⊎[_,_])
open import Data.Empty using (⊥-elim)
-- local library imports
open import Dodo.Unary
open import Dodo.Binary hiding (REL)
open import Burrow.Template.Arch as Π
-- Local imports
open import Helpers


record MixedExecution {arch : Arch} (ex : Execution {arch}) : Set₁ where
  open Π.Ev arch
  open Execution ex
  field
    -- # Definitions
    
    si : Rel₀ Event -- ^ Same Instruction relation


    -- # Wellformedness

    si-internal : si ⊆₂ (po ∪₂ flip po ∪₂ ⦗ events ⦘)
    -- basically, `si` is an equivalence relation.
    -- note that the `filter-rel events` is crucial here. otherwise we can prove
    -- false. pick an `x` ∉ events, construct `si x x`, construct `po x x` (with
    -- `si-internal`), construct `x ∈ events` (with `po-elements`). tada, ⊥.
    si-refl  : Reflexive (filter-rel events si)
    si-trans : Transitive si
    si-sym   : Symmetric si
    
    -- note: Fence events (and skips) are *only* `si` with themselves
    si-dom : si ⊆₂ (EvR ×₂ EvR) ∪₂ (EvW ×₂ EvW) ∪₂ ⦗ events ⦘


module Derived
  {arch : Arch}
  {ex : Execution {arch}}
  (mex : MixedExecution ex)
  where

  open Π.Ev arch
  open MixedExecution mex

  siʳ-r : {x y : Event} → EvR x → si x y → EvR y
  siʳ-r x-r si[xy] with ⊆₂-apply si-dom si[xy]
  ... | opt₁ (x-r , y-r) = y-r
  ... | opt₂ (x-w , y-w) = ⊥-elim (disjoint-r/w _ (x-r , x-w))
  ... | opf₃ (refl , _)  = x-r
  
  siʳ-w : {x y : Event} → EvW x → si x y → EvW y
  siʳ-w x-w si[xy] with ⊆₂-apply si-dom si[xy]
  ... | opt₁ (x-r , y-r) = ⊥-elim (disjoint-r/w _ (x-r , x-w))
  ... | opt₂ (x-w , y-w) = y-w
  ... | opf₃ (refl , _)  = x-w

  siʳ-rw : {x y : Event} → EvRW x → si x y → EvRW y
  siʳ-rw x-rw si[xy] =
    ⊎[ (λ x-r → r⇒rw (siʳ-r x-r si[xy]))
     , (λ x-w → w⇒rw (siʳ-w x-w si[xy]))
     ] (rw/rw x-rw)


module Properties
  {arch : Arch}
  {ex : Execution {arch}}
  (mex : MixedExecution ex)
  (wf : WellFormed ex)
  where

  open Execution ex
  open MixedExecution mex
  open Π.WfDefs wf


  si-elements : udr si ⇔₁ events
  si-elements = ⇔: proof-⊆ proof-⊇
    where
    proof-⊆ : udr si ⊆₁' events
    proof-⊆ x (opt₁ (y , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poˡ∈ex po[xy]
    ... | opt₂ po[yx] = poʳ∈ex po[yx]
    ... | opf₃ (_ , x∈ex) = x∈ex
    proof-⊆ y (opf₂ (x , si[xy])) with ⊆₂-apply si-internal si[xy]
    ... | opt₁ po[xy] = poʳ∈ex po[xy]
    ... | opt₂ po[yx] = poˡ∈ex po[yx]
    ... | opf₃ (refl , x∈ex) = x∈ex

    proof-⊇ : events ⊆₁' udr si
    proof-⊇ x x∈ex =
      let si[xx] = si-refl {with-pred x x∈ex}
      in opt₁ (x , si[xx])

  siˡ∈ex : si ˡ∈ex
  siˡ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₁ ∘ (_ ,_)

  siʳ∈ex : si ʳ∈ex
  siʳ∈ex = ⇔₁-apply-⊆₁ si-elements ∘ inj₂ ∘ (_ ,_)
