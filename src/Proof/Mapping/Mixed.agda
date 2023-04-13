{-# OPTIONS --safe #-}

-- External library imports
open import Burrow.Template.Mapping as Δ
open import Burrow.Framework.Mapping.Core using (MappingFramework)
open import Arch.Mixed as Mixed using (MixedExecution)


-- | Mapping definitions of the Mixed-Size extension
module Proof.Mapping.Mixed
  {archˢ archᵗ : Arch}
  {dst : Execution {archᵗ}}
  (dst-mex : MixedExecution dst)
  {dst-wf : WellFormed dst}
  (δ : MappingFramework archˢ dst-wf)
  where

-- stdlib imports
open import Relation.Unary using (_∈_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Function using (flip)
open import Data.Product using (_,_)
-- external library imports
open import Dodo.Binary
open MappingFramework δ
open import Burrow.Framework.Definition archˢ dst-wf using (GeneralFramework)
open GeneralFramework ψ
open import Burrow.Framework.Primitives dst-wf ev[⇐]
open import Burrow.Framework.WellFormed ψ using (rel[$⇒]; rel[⇐]; ev[⇐$]eq)
open import Burrow.Framework.Mapping.Definitions δ
-- local imports
open import Helpers


open Mixed.Properties dst-mex dst-wf
open MixedExecution dst-mex
open Execution


private
  Eventˢ = Event {archˢ}


src-si : Rel₀ Eventˢ
src-si = src-rel siˡ∈ex siʳ∈ex

si[$⇒] : Rel[$⇒] src-si si
si[$⇒] = rel[$⇒] siˡ∈ex siʳ∈ex

si[⇒] : Rel[⇒] src-si si
si[⇒] = [$⇒]→₂[⇒] si[$⇒]

si[⇐] : Rel[⇐] src-si si
si[⇐] = rel[⇐] siˡ∈ex siʳ∈ex

si[⇐$] : Rel[⇐$] src-si si
si[⇐$] = [⇐]→₂[⇐$] si[⇐]

siˡ∈src : {x y : Eventˢ} → src-si x y → x ∈ events src
siˡ∈src = relˡ∈src siˡ∈ex siʳ∈ex

siʳ∈src : {x y : Eventˢ} → src-si x y → y ∈ events src
siʳ∈src = relʳ∈src siˡ∈ex siʳ∈ex

src-si-internal : src-si ⊆₂ po src ∪₂ flip (po src) ∪₂ ⦗ events src ⦘
src-si-internal = ⊆: λ{x y si[xy]ˢ →
    let x∈src = siˡ∈src si[xy]ˢ
        y∈src = siʳ∈src si[xy]ˢ
        si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
    in
    case ⊆₂-apply si-internal si[xy]ᵗ of
    λ{ (opt₁ po[xy]ᵗ) → opt₁ (po[⇐$] x∈src y∈src po[xy]ᵗ)
     ; (opt₂ po[yx]ᵗ) → opt₂ (po[⇐$] y∈src x∈src po[yx]ᵗ)
     ; (opf₃ (x≡y , _)) → opf₃ (ev[⇐$]eq x∈src y∈src x≡y , x∈src)
     }
  }

src-si-refl : Reflexive (filter-rel (events src) src-si)
src-si-refl {with-pred xˢ x∈src} =
  let xᵗ = ev[⇒] x∈src
      x∈dst = events[⇒] x∈src
      si[xx]ᵗ = si-refl {with-pred xᵗ x∈dst}
  in si[⇐$] x∈src x∈src si[xx]ᵗ

src-si-sym : Symmetric src-si
src-si-sym {xˢ} {yˢ} si[xy]ˢ =
  let x∈src = siˡ∈src si[xy]ˢ
      y∈src = siʳ∈src si[xy]ˢ
      si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
      si[yx]ᵗ = si-sym si[xy]ᵗ
  in si[⇐$] y∈src x∈src si[yx]ᵗ

src-si-trans : Transitive src-si
src-si-trans {xˢ} {yˢ} {zˢ} si[xy]ˢ si[yz]ˢ =
  let x∈src = siˡ∈src si[xy]ˢ
      y∈src = siʳ∈src si[xy]ˢ
      z∈src = siʳ∈src si[yz]ˢ
      si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
      si[yz]ᵗ = si[⇒] y∈src z∈src si[yz]ˢ
      si[xz]ᵗ = si-trans si[xy]ᵗ si[yz]ᵗ
  in si[⇐$] x∈src z∈src si[xz]ᵗ

src-si-dom : src-si ⊆₂ (EvR ×₂ EvR) ∪₂ (EvW ×₂ EvW) ∪₂ ⦗ events src ⦘
src-si-dom = ⊆: (λ x y si[xy]ˢ →
    let x∈src = siˡ∈src si[xy]ˢ
        y∈src = siʳ∈src si[xy]ˢ
        si[xy]ᵗ = si[⇒] x∈src y∈src si[xy]ˢ
    in
    case ⊆₂-apply si-dom si[xy]ᵗ of
    λ{ (opt₁ (x-r , y-r)) → opt₁ (R[⇐$] x∈src x-r , R[⇐$] y∈src y-r)
     ; (opt₂ (x-w , y-w)) → opt₂ (W[⇐$] x∈src x-w , W[⇐$] y∈src y-w)
     ; (opf₃ (x≡y , _)) → opf₃ (ev[⇐$]eq x∈src y∈src x≡y , x∈src)
     }
  )

src-mex : MixedExecution src
src-mex =
  record {
    si          = src-si
  ; si-internal = src-si-internal
  ; si-refl     = λ {x} → src-si-refl {x}
  ; si-sym      = src-si-sym
  ; si-trans    = src-si-trans
  ; si-dom      = src-si-dom
  }
