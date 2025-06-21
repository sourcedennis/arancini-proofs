{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.Armv8 using (arch-Armv8; Armv8Execution)
open import MapAIMMtoArmv8 using (Armv8-AIMMRestricted)


module Proof.Mapping.AIMMtoArmv8
  {dst : Execution {arch-Armv8}}
  {dst-a8 : Armv8Execution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-AIMMRestricted dst-a8)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- External library imports
open import Dodo.Binary
-- Local imports: Architectures
import Arch.AIMM
open Arch.AIMM.Relations
-- Local imports: Theorem Definitions
open import MapAIMMtoArmv8 using (AIMM⇒Armv8) -- defines *what* we're proving
-- Local imports: Proofs Components
open import Proof.Mapping.AIMMtoArmv8.Execution dst-wf dst-ok as Ex -- defines δ (and ψ)
open import Proof.Mapping.AIMMtoArmv8.Consistent dst-wf dst-ok
open import Proof.Mapping.AIMMtoArmv8.Mapping dst-wf dst-ok
open import Proof.Mapping.Mixed (Armv8Execution.mix dst-a8) δ
open Δ.Final δ


proof-AIMM⇒Armv8 :
  ∃[ src ] ∃[ src-tex ]
    ( WellFormed src
    × IsAIMMConsistent {src} src-tex
    × AIMM⇒Armv8 src dst-a8
    × behavior src ⇔₂ behavior dst
    )
proof-AIMM⇒Armv8 =
  ( src
  , src-mex
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
