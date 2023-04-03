{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
-- Local imports
open import Arch.RISCV using (arch-RISCV; RISCVExecution)
open import MapTCGtoRISCV using (RISCV-TCGRestricted)


module Proof.Mapping.TCGtoRISCV
  {dst : Execution {arch-RISCV}}
  {dst-rv : RISCVExecution dst}
  (dst-wf : WellFormed dst)
  (dst-ok : RISCV-TCGRestricted dst-rv)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- External library imports
open import Dodo.Binary
-- Local imports: Architectures
import Arch.TCG
open Arch.TCG.Relations
-- Local imports: Theorem Definitions
open import MapTCGtoRISCV using (TCG⇒RISCV) -- defines *what* we're proving
-- Local imports: Proofs Components
open import Proof.Mapping.TCGtoRISCV.Execution dst-wf dst-ok as Ex -- defines δ (and ψ)
open import Proof.Mapping.TCGtoRISCV.Consistent dst-wf dst-ok
open import Proof.Mapping.TCGtoRISCV.Mapping dst-wf dst-ok
open Ex.Extra
open Δ.Final δ


proof-TCG⇒RISCV :
  ∃[ src ] ∃[ src-tex ]
    ( WellFormed src
    × IsTCGConsistent {src} src-tex
    × TCG⇒RISCV src dst-rv
    × behavior src ⇔₂ behavior dst
    )
proof-TCG⇒RISCV =
  ( src
  , Ex.Extra.src-tex
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
