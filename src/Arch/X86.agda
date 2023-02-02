{-# OPTIONS --safe #-}

module Arch.X86 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary using (_⇔_)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
open import Burrow.Template.Arch as Π
-- Local imports
open import Helpers


-- # Definitions

data LabR : Set where
  lab-r : Tag → LabR

data LabW : Set where
  lab-w : Tag → LabW

data LabF : Set where
  lab-f : LabF

lab-r-tag : LabR → Tag
lab-r-tag (lab-r tag) = tag

lab-w-tag : LabW → Tag
lab-w-tag (lab-w tag) = tag

lab-r-dec≡ : Dec≡ LabR
lab-r-dec≡ (lab-r t₁) (lab-r t₂) = cong-dec lab-r (λ{refl → refl}) (tag-dec≡ t₁ t₂)

lab-w-dec≡ : Dec≡ LabW
lab-w-dec≡ (lab-w t₁) (lab-w t₂) = cong-dec lab-w (λ{refl → refl}) (tag-dec≡ t₁ t₂)

lab-f-dec≡ : Dec≡ LabF
lab-f-dec≡ lab-f lab-f = yes refl

arch-x86 : Arch
arch-x86 =
  record
    { LabR       = LabR
    ; LabW       = LabW
    ; LabF       = LabF
    ; lab-r-tag  = lab-r-tag
    ; lab-w-tag  = lab-w-tag
    ; lab-r-dec≡ = lab-r-dec≡
    ; lab-w-dec≡ = lab-w-dec≡
    ; lab-f-dec≡ = lab-f-dec≡
    }

open Π.Ev arch-x86

EventX86 = Event -- note that this is parametrized over `arch-x86`


module Relations (ex : Execution {arch-x86}) where

  open Π.Defs ex


  data Implied (x y : Event) : Set where
    implied-pof : ( po ⨾ ⦗ dom rmw ∪₁ EvF ⦘ )   x y → Implied x y
    implied-fpo : ( ⦗ codom rmw ∪₁ EvF ⦘ ⨾ po ) x y → Implied x y

  -- X86 Preserved Program Order
  data Xppo (x y : Event) : Set where
    xppo-w×w : ( (EvW ×₂ EvW) ∩₂ po ) x y → Xppo x y
    xppo-r×w : ( (EvR ×₂ EvW) ∩₂ po ) x y → Xppo x y
    xppo-r×r : ( (EvR ×₂ EvR) ∩₂ po ) x y → Xppo x y

  -- X86 Happens Before
  data Xhb (x y : Event) : Set where
    xhb-xppo    : Xppo    x y → Xhb x y
    xhb-implied : Implied x y → Xhb x y
    xhb-rfe     : rfe     x y → Xhb x y
    xhb-fr      : fr      x y → Xhb x y
    xhb-co      : co      x y → Xhb x y

  record IsX86Consistent : Set where
    field
      -- # Consistency axioms

      ax-coherence  : Acyclic _≡_ ( po-loc ∪₂ rf ∪₂ fr ∪₂ co )
      ax-atomicity  : Empty₂ (rmw ∩₂ (fre ⨾ coe))
      ax-ghb        : Acyclic _≡_ Xhb
