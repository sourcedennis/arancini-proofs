{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.TCG using (arch-TCG)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG
  {dst : Execution {arch-TCG}}
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
import Arch.X86
open Arch.X86.Relations
-- External library imports
open import Dodo.Binary
-- Local imports: Theorem Definitions
open import MapX86toTCG using (X86⇒TCG) -- defines *what* we're proving
-- Local imports: Proof Components
open import Proof.Mapping.X86toTCG.Execution dst-wf dst-ok -- defines δ (and ψ)
open import Proof.Mapping.X86toTCG.Consistent dst-wf dst-ok
open import Proof.Mapping.X86toTCG.Mapping dst-wf dst-ok
open Δ.Final δ


proof-X86⇒TCG :
  ∃[ src ]
    ( WellFormed src
    × IsX86Consistent src
    × X86⇒TCG src dst
    × behavior src ⇔₂ behavior dst
    )
proof-X86⇒TCG =
  ( src
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
