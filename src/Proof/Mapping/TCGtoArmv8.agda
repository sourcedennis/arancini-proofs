{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapTCGtoArmv8 using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8
  {dst : Execution {arch-Armv8}}
  {dst-a8 : Armv8Execution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst-a8)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- External library imports
open import Dodo.Binary
-- Local imports: Architectures
import Arch.TCG
open Arch.TCG.Relations
-- Local imports: Theorem Definitions
open import MapTCGtoArmv8 using (TCG⇒Armv8) -- defines *what* we're proving
-- Local imports: Proofs Components
open import Proof.Mapping.TCGtoArmv8.Execution dst-wf dst-ok as Ex -- defines δ (and ψ)
open import Proof.Mapping.TCGtoArmv8.Consistent dst-wf dst-ok
open import Proof.Mapping.TCGtoArmv8.Mapping dst-wf dst-ok
open import Proof.Mapping.Mixed (Armv8Execution.mix dst-a8) δ
open Δ.Final δ


proof-TCG⇒Armv8 :
  ∃[ src ] ∃[ src-tex ]
    ( WellFormed src
    × IsTCGConsistent {src} src-tex
    × TCG⇒Armv8 src dst-a8
    × behavior src ⇔₂ behavior dst
    )
proof-TCG⇒Armv8 =
  ( src
  , src-mex
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
