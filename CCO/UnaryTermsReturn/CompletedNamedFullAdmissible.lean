import CCO.UnaryTermsReturn.CompletedNamedLabelledSignature
import Mathlib.Data.Set.Card

/-!
# B052 C14: exact full-diagram unary-admissibility receiving interface

The partial source has every original terminal unary symbol as a
LABELLED transition graph. Its one-generated closure is the LEAST
reachable set under those genuine labels, not an arbitrary small subset.
The ACTUAL witness is a finite unary-closed induced member of the
literal original real/represented-quotient carrier.

For EVERY root, source10 unary-admissibility supplies an isomorphism
of the WHOLE induced closure, preserving each named unary graph,
literal equality and each binary predicate. The binary predicate
interpretation is supplied by the genuine hidden-language consumer;
this module does not manufacture it. The bound is transported along
the FULL diagram equivalence, not from size-only admissibility.

No arbitrary total-unary partial input is claimed admissible; nor is
hidden SAP, hidden homogeneity, or an HN theorem asserted.
-/

universe u v w t p b q

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Literal finite-word reachability under the full labelled
unary language of a PARTIAL source. This does not impose the
identities of the genuine old quotient model on an arbitrary source. -/
inductive PartialNamedReachable
    {P : Type p} {U : Type q}
    (step : U → P → P → Prop) : P → P → Prop where
  | refl (x : P) : PartialNamedReachable step x x
  | next {x y z : P} (h : PartialNamedReachable step x y)
      (s : U) (e : step s y z) : PartialNamedReachable step x z

/-- This is the genuine least one-generated function-graph
closure, with the literal identity as its empty word. -/
def partialNamedClosure
    {P : Type p} {U : Type q}
    (step : U → P → P → Prop) (x : P) : Set P :=
  {y | PartialNamedReachable step x y}

theorem partial_named_closure_contains
    {P : Type p} {U : Type q}
    (step : U → P → P → Prop) (x : P) :
    x ∈ partialNamedClosure step x :=
  PartialNamedReachable.refl x

theorem partial_named_closure_closed
    {P : Type p} {U : Type q}
    (step : U → P → P → Prop) (x : P)
    (s : U) {y z : P} (hy : y ∈ partialNamedClosure step x)
    (e : step s y z) :
    z ∈ partialNamedClosure step x :=
  PartialNamedReachable.next hy s e

theorem partial_named_closure_minimal
    {P : Type p} {U : Type q}
    (step : U → P → P → Prop) (x : P)
    (C : Set P) (hx : x ∈ C)
    (hClosed : ∀ (s : U) {y z : P}, y ∈ C →
      step s y z → z ∈ C) :
    partialNamedClosure step x ⊆ C := by
  intro y hy
  induction hy with
  | refl => exact hx
  | next h s e ih => exact hClosed s ih e

/-- Source10's FULL one-generator witness, including the actual
finite completed member and its total unary-closed induced
subdiagram. The equivalence preserves each true named unary
function graph and every binary relation named by B. The
actual binary interpretation must be supplied by the terminal
hidden-language consumer; it is not assumed trivial. -/
structure OriginalCompletedFullGeneratorIso
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type p} {B : Type b}
    (partialStep : OriginalCompletedPrimitiveSymbol S H →
      P → P → Prop)
    (partialBinary : B → P → P → Prop)
    (actualBinary : B →
      OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop)
    (root : P) where
  actualMember : Set (OriginalCompletedNamedCarrier S H)
  finiteMember : actualMember.Finite
  closedMember : OriginalCompletedNamedStepClosed
    S H sap nr2 actualMember
  actualRoot : actualMember
  toEquiv :
    (partialNamedClosure partialStep root) ≃
      {y : actualMember |
        OriginalCompletedNamedRestrictedReachable
          S H sap nr2 actualMember actualRoot y}
  preservesUnary : ∀ (s : OriginalCompletedPrimitiveSymbol S H)
      (x y : partialNamedClosure partialStep root),
    partialStep s x.val y.val ↔
      OriginalCompletedNamedLabelledStep S H sap nr2 s
        (toEquiv x).val.val (toEquiv y).val.val
  preservesBinary : ∀ (b : B)
      (x y : partialNamedClosure partialStep root),
    partialBinary b x.val y.val ↔
      actualBinary b (toEquiv x).val.val (toEquiv y).val.val

/-- The REAL content of D05: for every partial source vertex
there exists a full induced one-generated diagram isomorphism
to some ACTUAL finite completed old real/hidden member. The
whole partial source need not be completed or completable. -/
def OriginalCompletedFullyUnaryAdmissible
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type p} {B : Type b}
    (partialStep : OriginalCompletedPrimitiveSymbol S H →
      P → P → Prop)
    (partialBinary : B → P → P → Prop)
    (actualBinary : B →
      OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop) : Prop :=
  ∀ x : P, Nonempty
    (OriginalCompletedFullGeneratorIso S H sap nr2
      partialStep partialBinary actualBinary x)

/-- C14 source-facing size transfer for a specific actual FULL
unary/binary diagram isomorphism. Literal equivalence preserves
cardinality; the actual finite completed-member receiver supplies
the already proved uniform bound. -/
theorem original_completed_full_generator_iso_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type p} {B : Type b}
    (partialStep : OriginalCompletedPrimitiveSymbol S H →
      P → P → Prop)
    (partialBinary : B → P → P → Prop)
    (actualBinary : B →
      OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop)
    (x : P)
    (e : OriginalCompletedFullGeneratorIso S H sap nr2
      partialStep partialBinary actualBinary x) :
    (partialNamedClosure partialStep x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  letI : Finite e.actualMember := e.finiteMember.to_subtype
  have hCard :
      (partialNamedClosure partialStep x).ncard =
      ({y : e.actualMember |
        OriginalCompletedNamedRestrictedReachable
          S H sap nr2 e.actualMember e.actualRoot y}).ncard :=
    Set.ncard_congr' e.toEquiv
  rw [hCard]
  exact original_completed_finite_induced_generator_uniform
    S H sap nr2 e.actualMember e.closedMember e.actualRoot

/-- For EVERY root of a unary-admissible partial source, its
complete one-generated closure has at most the true m_typ
vertices. No assertion is made for arbitrary total-unary inputs. -/
theorem original_completed_fully_unary_admissible_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type p} {B : Type b}
    (partialStep : OriginalCompletedPrimitiveSymbol S H →
      P → P → Prop)
    (partialBinary : B → P → P → Prop)
    (actualBinary : B →
      OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop)
    (hAdmissible : OriginalCompletedFullyUnaryAdmissible
      S H sap nr2 partialStep partialBinary actualBinary)
    (x : P) :
    (partialNamedClosure partialStep x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  obtain ⟨e⟩ := hAdmissible x
  exact original_completed_full_generator_iso_uniform
    S H sap nr2 partialStep partialBinary actualBinary x e

end CCO.UnaryTermsReturn
