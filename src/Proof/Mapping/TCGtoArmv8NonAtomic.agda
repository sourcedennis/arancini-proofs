{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic
  {dst : Execution {arch-Armv8}}
  (dst-a8 : Armv8Execution)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst dst-a8)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
import Arch.TCG
open Arch.TCG.Relations
-- External library imports
open import Dodo.Binary
-- Local imports: Theorem Definitions
open import MapTCGtoArmv8NonAtomic using (TCG⇒Armv8) -- defines *what* we're proving
-- Local imports: Proof Components
open import Proof.Mapping.TCGtoArmv8NonAtomic.Execution dst-a8 dst-wf dst-ok -- defines δ (and ψ)
open import Proof.Mapping.TCGtoArmv8NonAtomic.Consistent dst-a8 dst-wf dst-ok
open import Proof.Mapping.TCGtoArmv8NonAtomic.Mapping dst-a8 dst-wf dst-ok
open Δ.Final δ


proof-TCG⇒Armv8 :
  ∃[ src ]
    ( WellFormed src
    × IsTCGConsistent src
    × TCG⇒Armv8 src dst dst-a8
    × behavior src ⇔₂ behavior dst
    )
proof-TCG⇒Armv8 =
  ( src
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
