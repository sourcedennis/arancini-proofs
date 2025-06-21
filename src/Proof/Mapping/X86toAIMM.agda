{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.AIMM using (arch-AIMM)
open import Arch.Mixed using (MixedExecution)
open import MapX86toAIMM using (AIMM-X86Restricted)


module Proof.Mapping.X86toAIMM
  {dst : Execution {arch-AIMM}}
  {dst-tex : MixedExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : AIMM-X86Restricted dst-tex)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
import Arch.X86
open Arch.X86.Relations
-- External library imports
open import Dodo.Binary
-- Local imports: Theorem Definitions
open import MapX86toAIMM using (X86⇒AIMM) -- defines *what* we're proving
-- Local imports: Proof Components
open import Proof.Mapping.X86toAIMM.Execution dst-wf dst-ok as Ex -- defines δ (and ψ)
open import Proof.Mapping.X86toAIMM.Consistent dst-wf dst-ok
open import Proof.Mapping.X86toAIMM.Mapping dst-wf dst-ok
open import Proof.Mapping.Mixed dst-tex δ
open Δ.Final δ


proof-X86⇒AIMM :
  ∃[ src ] ∃[ src-xex ]
    ( WellFormed src
    × IsX86Consistent {src} src-xex
    × X86⇒AIMM src dst
    × behavior src ⇔₂ behavior dst
    )
proof-X86⇒AIMM =
  ( src
  , src-mex
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
