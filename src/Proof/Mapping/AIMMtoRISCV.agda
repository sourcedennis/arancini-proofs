{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.RISCV using (arch-RISCV; RISCVExecution)
open import MapAIMMtoRISCV using (RISCV-AIMMRestricted)


module Proof.Mapping.AIMMtoRISCV
  {dst : Execution {arch-RISCV}}
  {dst-rv : RISCVExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : RISCV-AIMMRestricted dst-rv)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- External library imports
open import Dodo.Binary
-- Local imports: Architectures
import Arch.AIMM
open Arch.AIMM.Relations
-- Local imports: Theorem Definitions
open import MapAIMMtoRISCV using (AIMM⇒RISCV) -- defines *what* we're proving
-- Local imports: Proofs Components
open import Proof.Mapping.AIMMtoRISCV.Execution dst-wf dst-ok as Ex -- defines δ (and ψ)
open import Proof.Mapping.AIMMtoRISCV.Consistent dst-wf dst-ok
open import Proof.Mapping.AIMMtoRISCV.Mapping dst-wf dst-ok
open Ex.Extra
open Δ.Final δ


proof-AIMM⇒RISCV :
  ∃[ src ] ∃[ src-tex ]
    ( WellFormed src
    × IsAIMMConsistent {src} src-tex
    × AIMM⇒RISCV src dst-rv
    × behavior src ⇔₂ behavior dst
    )
proof-AIMM⇒RISCV =
  ( src
  , Ex.Extra.src-tex
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
