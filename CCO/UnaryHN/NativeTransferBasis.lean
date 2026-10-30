import PartiteConstruction.Functional.SingletonExpansion
import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! Concrete one-sorted interfaces for the original partial-function HN
transfer.  The native EHN map preserves positive incidences and embeds EVERY
actual closed irreducible source.  In unary languages its function law is
proved below to be full, including reflection of undefined domains; this
does not make the whole map injective or globally induced.

All finite completions below are actual members on their entire carrier.
The local test charges the cardinality of the original CLOSED subset.
-/

universe u v w
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

abbrev Class (L : Language.{u}) := StructureClass.{u,v} (L := L)

/-- Genuine original-partial HE, with all actual closed irreducible tests. -/
abbrev HE {L : Language.{u}} {V W : Type v}
    (C : Structure L V) (D : Structure L W) (f : V → W) : Prop :=
  C.IsEHNHomomorphismEmbedding D f

def Unary (L : Language.{u}) : Prop := ∀ F, L.funcArity F = 1

def Hereditary {L : Language.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} {C : Structure L V} {D : Structure L W},
    K D → Embedding C D → K C

/-- Actual finite hereditary SAP, including spans over empty closed bases.
The last clause records exact overlap; no freeness of the target is asserted. -/
structure FiniteHereditarySAP {L : Language.{u}} (K : Class.{u,v} L) : Prop where
  finite : ∀ {V : Type v} (C : Structure L V), K C → Finite V
  singleton : ∀ {V : Type v} (C : Structure L V), K C → C.SingletonValued
  hereditary : Hereditary K
  strong : ∀ {H V W : Type v}
      {Root : Structure L H} {Left : Structure L V} {Right : Structure L W},
    K Left → K Right →
    ∀ (sL : Embedding Root Left) (sR : Embedding Root Right),
    ∃ (X : Type v) (_ : Finite X) (Target : Structure L X),
      K Target ∧ ∃ (jL : Embedding Left Target) (jR : Embedding Right Target),
        (∀ h, jL (sL h) = jR (sR h)) ∧
        (∀ x y, jL x = jR y → ∃ h, x = sL h ∧ y = sR h)

def AllIrreducible {L : Language.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V : Type v} (C : Structure L V), K C → C.Irreducible

/-- This is actual membership, not existence of a later completion. -/
def IrreduciblesIn {L : Language.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Structure L V) : Prop :=
  ∀ {X : Type v} (E : Structure L X), E.Irreducible → Embedding E C → K E

def HasCompletion {L : Language.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (D : Structure L W),
    K D ∧ ∃ f : V → W, HE C D f

/-- STRONG means globally injective HE. It does not mean globally induced. -/
def HasStrongCompletion {L : Language.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (D : Structure L W),
    K D ∧ ∃ f : V → W, HE C D f ∧ Function.Injective f

def ClosedSmallCompletable {L : Language.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Structure L V) (n : ℕ) : Prop :=
  ∀ (S : Finset V), S.card ≤ n → ∀ hS : C.IsClosed (↑S : Set V),
    HasCompletion K (C.induce (↑S : Set V) hS)

/-- Original HN Definition 2.8. The cutoff is fixed from the original C₀
before the candidate; only actual closed functional substructures are tested. -/
def LocallyFinite {L : Language.{u}} (K R : Class.{u,v} L) : Prop :=
  ∀ {P : Type v} [Finite P] (C₀ : Structure L P), R C₀ →
    ∃ n : ℕ, ∀ {V : Type v} [Finite V] (C : Structure L V),
      C.SingletonValued → (∃ p : V → P, HE C C₀ p) →
      IrreduciblesIn K C → ClosedSmallCompletable K C n → HasCompletion K C

def Ramsey {L : Language.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} [Finite V] [Finite W]
    (A : Structure L V) (B : Structure L W), K A → K B →
    ∀ (κ : Type w) [Fintype κ] [Nonempty κ],
      ∃ (X : Type v) (_ : Finite X) (C : Structure L X),
        K C ∧ Structure.Arrow A B C κ

theorem HasStrongCompletion.to_completion {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure L V} (h : HasStrongCompletion K C) :
    HasCompletion K C := by
  obtain ⟨W, hW, D, hD, f, hf, _⟩ := h
  exact ⟨W, hW, D, hD, f, hf⟩

theorem HasCompletion.of_embedding {L : Language.{u}} {K : Class.{u,v} L}
    {V W : Type v} {C : Structure L V} {D : Structure L W}
    (hD : HasCompletion K D) (e : Embedding C D) : HasCompletion K C := by
  obtain ⟨X, hX, T, hT, f, hf⟩ := hD
  exact ⟨X, hX, T, hT, f ∘ e, hf.comp e.isEHNHomomorphismEmbedding⟩

theorem HasCompletion.of_mem {L : Language.{u}} {K : Class.{u,v} L}
    (hK : FiniteHereditarySAP K) {V : Type v} {C : Structure L V} (hC : K C) :
    HasCompletion K C :=
  ⟨V, hK.finite C hC, C, hC, id, (Embedding.id C).isEHNHomomorphismEmbedding⟩

theorem irreduciblesIn_of_mem {L : Language.{u}} {K : Class.{u,v} L}
    (hK : Hereditary K) {V : Type v} {C : Structure L V} (hC : K C) :
    IrreduciblesIn K C :=
  fun _ _ e => hK hC e

end CCO.UnaryHN.Native
