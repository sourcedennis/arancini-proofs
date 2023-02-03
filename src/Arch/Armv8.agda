{-# OPTIONS --safe #-}


-- | The Armv8 model as obtained from the "Armed Cats" paper,
-- with our proposed change to the `amo` case in the `bob` relation.
module Arch.Armv8 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) renaming (sym to ≡-sym)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
open import Burrow.Template.Arch as Π
-- Local imports
open import Helpers


open Tag


-- Notes on model:
--
-- RMW creates R and W events
-- RMW_A creates A and W events
-- RMW_L creates A and L events

data F-mode : Set where
  F-full : F-mode
  F-ld   : F-mode
  F-st   : F-mode

data LabR : Set where
  lab-r : Tag → LabR
  lab-a : Tag → LabR -- ^ acquire read
  lab-q : LabR -- ^ acquirePC read (always tmov)

data LabW : Set where
  lab-w : Tag → LabW -- ^ write
  lab-l : Tag → LabW -- ^ release write

data LabF : Set where
  lab-f   : F-mode → LabF -- ^ fence
  lab-isb : LabF -- ^ ISB (control) fence

lab-r-tag : LabR → Tag
lab-r-tag (lab-r tag) = tag
lab-r-tag (lab-a tag) = tag
lab-r-tag lab-q       = tmov

lab-w-tag : LabW → Tag
lab-w-tag (lab-w tag) = tag
lab-w-tag (lab-l tag) = tag

lab-r-dec≡ : Dec≡ LabR
lab-r-dec≡ (lab-r t₁)   (lab-r t₂) = cong-dec lab-r (λ{refl → refl}) (tag-dec≡ t₁ t₂)
lab-r-dec≡ (lab-a t₁)   (lab-a t₂) = cong-dec lab-a (λ{refl → refl}) (tag-dec≡ t₁ t₂)
lab-r-dec≡ lab-q        lab-q      = yes refl
lab-r-dec≡ (lab-r _)    (lab-a _)  = no (λ ())
lab-r-dec≡ (lab-r _)    lab-q      = no (λ ())
lab-r-dec≡ (lab-a _)    (lab-r _)  = no (λ ())
lab-r-dec≡ (lab-a _)    lab-q      = no (λ ())
lab-r-dec≡ lab-q        (lab-r _)  = no (λ ())
lab-r-dec≡ lab-q        (lab-a _)  = no (λ ())

lab-w-dec≡ : Dec≡ LabW
lab-w-dec≡ (lab-w t₁) (lab-w t₂) = cong-dec lab-w (λ{refl → refl}) (tag-dec≡ t₁ t₂)
lab-w-dec≡ (lab-l t₁) (lab-l t₂) = cong-dec lab-l (λ{refl → refl}) (tag-dec≡ t₁ t₂)
lab-w-dec≡ (lab-w _)  (lab-l _)  = no (λ ())
lab-w-dec≡ (lab-l _)  (lab-w _)  = no (λ ())

fence-dec≡ : Dec≡ F-mode
fence-dec≡ F-full F-full = yes refl
fence-dec≡ F-ld   F-ld   = yes refl
fence-dec≡ F-st   F-st   = yes refl
-- false cases
fence-dec≡ F-full F-ld   = no (λ ())
fence-dec≡ F-full F-st   = no (λ())
fence-dec≡ F-ld   F-full = no (λ())
fence-dec≡ F-ld   F-st   = no (λ())
fence-dec≡ F-st   F-full = no (λ())
fence-dec≡ F-st   F-ld   = no (λ())

lab-f-dec≡ : Dec≡ LabF
lab-f-dec≡ (lab-f m₁) (lab-f m₂) = cong-dec lab-f (λ{refl → refl}) (fence-dec≡ m₁ m₂)
lab-f-dec≡ lab-isb    lab-isb    = yes refl
lab-f-dec≡ (lab-f _)  lab-isb    = no (λ ())
lab-f-dec≡ lab-isb    (lab-f _)  = no (λ ())

arch-Armv8 : Arch
arch-Armv8 =
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



open Π.Ev arch-Armv8

EventArmv8 = Event -- note that this is parameterized over `arch-Armv8`


private
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    tag : Tag

-- | release write
data EvL : Pred₀ Event where
  ev-l : EvL (event-w uid tid loc val (lab-l tag))

-- | acquire read
data EvA : Pred₀ Event where
  ev-a : EvA (event-r uid tid loc val (lab-a tag))

-- | release write indexed by tag
data EvLₜ (tag : Tag) : Pred₀ Event where
  ev-l : EvLₜ tag (event-w uid tid loc val (lab-l tag))

-- acquire read indexed by tag
data EvAₜ (tag : Tag) : Pred₀ Event where
  ev-a : EvAₜ tag (event-r uid tid loc val (lab-a tag))

-- | acquirePC read
data EvQ : Pred₀ Event where
  ev-q : EvQ (event-r uid tid loc val lab-q)

data EvISB : Pred₀ Event where
  ev-isb : EvISB (event-f uid tid lab-isb)

EvFₘ : F-mode → Pred₀ Event
EvFₘ = EvFₜ ∘ lab-f


record Armv8Execution : Set₁ where
  field
    -- # Armv8-specific relations

    data₋ : Rel₀ Event -- called `data₋`, because `data` is a keyword
    addr  : Rel₀ Event
    ctrl  : Rel₀ Event

    -- rmw relation that is created by single-instruction RMWs
    amo  : Rel₀ Event
    -- rmw relation that is created by load-linked/store-conditional RMWs.
    lxsx : Rel₀ Event


-- open import Burrow.Execution {arch-Armv8} using (Execution)

module Relations (ex : Execution {arch-Armv8}) (a8 : Armv8Execution) where

  open Π.Defs ex
  open Armv8Execution a8


  InterveningWrite : Rel₀ Event → Rel₀ Event
  InterveningWrite R = R ⨾ ⦗ EvW ⦘ ⨾ R

  -- | Local read successor
  lrs : Rel₀ Event
  lrs = ⦗ EvW ⦘ ⨾ (po-loc \₂ InterveningWrite po-loc) ⨾ ⦗ EvR ⦘

  -- | Local write successor
  lws : Rel₀ Event
  lws = po-loc ⨾ ⦗ EvW ⦘

  -- | Coherence after
  --
  -- Intuitively, a write is coherence-after another event, if it overwrites its value.
  data Ca (x y : Event) : Set where
    ca-co : co x y → Ca x y -- w × w
    ca-fr : fr x y → Ca x y -- r × w . rf⁻¹;co

  -- | Observed by
  data Obs (x y : Event) : Set where
    obs-rfe : rfe x y → Obs x y
    obs-ca  : Ca  x y → Obs x y

  -- | Barrier-ordered-before
  --
  -- Consider this the union over all relations in it's constructors.
  --
  -- This data structure is much easier to handle than taking _∪₂_ over all,
  -- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
  data Bob (x y : Event) : Set where
    bob-f   : ( po ⨾ ⦗ EvFₘ F-full ⦘ ⨾ po )                   x y → Bob x y
    bob-la  : ( ⦗ EvL ⦘ ⨾ po ⨾ ⦗ EvA ⦘ )                      x y → Bob x y
    bob-fld : ( ⦗ EvR ⦘ ⨾ po ⨾ ⦗ EvFₘ F-ld ⦘ ⨾ po )           x y → Bob x y
    bob-fst : ( ⦗ EvW ⦘ ⨾ po ⨾ ⦗ EvFₘ F-st ⦘ ⨾ po ⨾ ⦗ EvW ⦘ ) x y → Bob x y
    bob-acq : ( ⦗ EvA ∪₁ EvQ ⦘ ⨾ po )                         x y → Bob x y
    bob-rel : ( po ⨾ ⦗ EvL ⦘ )                                x y → Bob x y
    bob-amo : ( ⦗ codom ( ⦗ EvA ⦘ ⨾ amo ⨾ ⦗ EvL ⦘ ) ⦘ ⨾ po )  x y → Bob x y
    -- Note: Doesn't use our other `amo` rule
    -- bob-amoˡ : ( po ⨾ ⦗ dom ( ⦗ EvA ⦘ ⨾ amo ⨾ ⦗ EvL ⦘ ) ⦘ )   x y → Bob x y

  -- | Data ordered before
  data Dob (x y : Event) : Set where
    dob-addr    : addr                                                     x y → Dob x y
    dob-data    : data₋                                                    x y → Dob x y
    dob-ctrl    : ( ctrl ⨾ ⦗ EvW ⦘ )                                       x y → Dob x y
    dob-isb     : ( ( ctrl ∪₂ ( addr ⨾ po ) ) ⨾ ⦗ EvISB ⦘ ⨾ po ⨾ ⦗ EvR ⦘ ) x y → Dob x y
    dob-addr-po : ( addr ⨾ po ⨾ ⦗ EvW ⦘ )                                  x y → Dob x y
    dob-lrs     : ( ( addr ∪₂ data₋ ) ⨾ lrs )                              x y → Dob x y

  -- | Atomic ordered before
  data Aob (x y : Event) : Set where
    aob-rmw : rmw                            x y → Aob x y
    -- `lrs` changed from: ( ⦗ codom rmw ⦘ ⨾ lrs ⨾ ⦗ EvA ∪₁ EvQ ⦘ ) x y → Aob x y
    aob-lrs : ( rmw ⨾ lrs ⨾ ⦗ EvA ∪₁ EvQ ⦘ ) x y → Aob x y

  -- | Immediate Locally-ordered-before
  data Lobi (x y : Event) : Set where
    lobi-init : ( ⦗ EvInit ⦘ ⨾ po ) x y → Lobi x y
    -- TODO: lws is now: lws ; si
    lobi-lws  : lws                 x y → Lobi x y
    lobi-dob  : Dob                 x y → Lobi x y
    lobi-aob  : Aob                 x y → Lobi x y
    lobi-bob  : Bob                 x y → Lobi x y
    -- missing `pob`. TODO

  -- Locally-ordered-before
  Lob : Rel₀ Event
  Lob = TransClosure Lobi

  -- Immediate Ordered before
  data Obi (x y : Event) : Set where
    -- TODO: Obs ; si
    obi-obs : Obs x y → Obi x y
    obi-lob : Lob x y → Obi x y

  -- Ordered before
  Ob : Rel₀ Event
  Ob = TransClosure Obi


  record IsArmv8Consistent : Set where
    field
      -- # Armv8-specific relations

      -- The `rmw` relation is obtained either by atomic read-modify-write instructions (amo)
      -- or load-linked/store-conditional instruction pairs.
      amo-lxsx-def : rmw  ⇔₂  amo ∪₂ lxsx

      data-def₁ : data₋ ⊆₂ EvR ×₂ EvW
      data-def₂ : data₋ ⊆₂ po
      addr-def₁ : addr  ⊆₂ EvR ×₂ ( EvR ∪₁ EvW )
      addr-def₂ : data₋ ⊆₂ po
      ctrl-def₁ : ctrl  ⊆₂ EvR ×₂ EvE
      ctrl-def₂ : ctrl  ⊆₂ po
      ctrl-def₃ : ( ctrl ⨾ po ) ⊆₂ ctrl

      -- # Armv8-specific consistency constraints

      ax-internal-rw : Irreflexive _≡_ ( ⦗ EvR ⦘ ⨾ ( po-loc ∪₂ rmw ) ⨾ ⦗ EvW ⦘ ⨾ rfi ⨾ ⦗ EvR ⦘ )
      ax-internal-ww : Irreflexive _≡_ ( ⦗ EvW ⦘ ⨾ po-loc ⨾ ⦗ EvW ⦘ ⨾ Ca ⨾ ⦗ EvW ⦘ )
      ax-internal-wr : Irreflexive _≡_ ( ⦗ EvW ⦘ ⨾ po-loc ⨾ ⦗ EvR ⦘ ⨾ Ca ⨾ ⦗ EvW ⦘ )

      ax-atomicity  : Empty₂ ( rmw ∩₂ (fre ⨾ coe) )
      ax-external : Irreflexive _≡_ Ob -- "External Visibility"

  open IsArmv8Consistent


  -- # Helpers

  amo-def : IsArmv8Consistent → amo ⊆₂ rmw
  amo-def = ∪₂-elimʳ-⊆₂ ∘ ⇔₂-to-⊇₂ ∘ amo-lxsx-def

  lxsx-def : IsArmv8Consistent → lxsx ⊆₂ rmw
  lxsx-def = ∪₂-elimˡ-⊆₂ ∘ ⇔₂-to-⊇₂ ∘ amo-lxsx-def
