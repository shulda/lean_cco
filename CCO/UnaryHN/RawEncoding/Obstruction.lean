import CCO.UnaryHN.RawEncoding.Typing
import CCO.UnaryHN.RawEncoding.PairCoverage
import CCO.UnaryHN.Obstruction

/-! Exact typed obstruction premises and their genuine one-sorted discharge.
N is an INTEGER, the tested subset is ACTUALLY CLOSED, and its original
cardinality is unchanged. No closure-size or arbitrary-malformed-source bound
is assumed or concluded. -/
universe u v
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)

def RestrictedObstruction {L : Signature.{u}} (K : Class.{u,v} L) (N : ℤ) : Prop :=
  ∀ {V : Type v} [Finite V] (C : Typed L V), IrreduciblesIn K C →
    ¬ HasCompletion K C → ∃ (S : Finset V) (hS : C.IsClosed (↑S : Set V)),
      (S.card : ℤ) ≤ N ∧ ¬ HasCompletion K (C.induce (↑S : Set V) hS)

def OneGeneratedDomain {L : Signature.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Typed L V) : Prop := ∀ x, K (C.singletonStructure x)

def DirectObstruction {L : Signature.{u}} (K : Class.{u,v} L) (N : ℤ) : Prop :=
  ∀ {V : Type v} [Finite V] (C : Typed L V), OneGeneratedDomain K C →
    ¬ HasCompletion K C → ∃ (S : Finset V) (hS : C.IsClosed (↑S : Set V)),
      (S.card : ℤ) ≤ N ∧ ¬ HasCompletion K (C.induce (↑S : Set V) hS)

/-- The bound is used only AFTER raw local completed membership has proved
typing, with actual induced subsets, exact domains, and the SAME vertex set. -/
theorem encoded_restrictedObstruction {L : Signature.{u}} {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) {N : ℤ} (hN : RestrictedObstruction K N) :
    Native.RestrictedObstruction (EncodedClass K) N := by
  intro V hV D _hSingle hPieces hNo
  obtain ⟨C, hEncode, _hTotal⟩ := typed_of_irreducibles hCompleted D hPieces
  subst D
  have hTypedPieces : IrreduciblesIn K C := (irreduciblesIn_encode_iff C).mp hPieces
  have hTypedNo : ¬ HasCompletion K C :=
    fun h => hNo ((completion_encode_iff C).mpr h)
  obtain ⟨S, hS, hSize, hBad⟩ := hN C hTypedPieces hTypedNo
  refine ⟨S, (closed_encode_iff C _).mpr hS, hSize, ?_⟩
  intro hSmall
  apply hBad
  apply (completion_encode_iff (C.induce (↑S : Set V) hS)).mp
  rw [encode_induce]
  exact hSmall

/-- C37: the ONLY B034 inputs are actual singleton membership and totality.
There is no optional m-bound, hidden-coordinate provider or completion proxy. -/
theorem oneGenerated_of_irreducibles {L : Signature.{u}} {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) {V : Type v} [Finite V] (C : Typed L V)
    (hPieces : IrreduciblesIn K C) : OneGeneratedDomain K C ∧ C.Total :=
  b034_singleton_and_total hCompleted hPieces

/-- C38: prove the main restricted premise from the direct premise rather
than keeping them as two independent hypotheses. -/
theorem restricted_of_direct {L : Signature.{u}} {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) {N : ℤ} (hN : DirectObstruction K N) :
    RestrictedObstruction K N := by
  intro V hV C hPieces hNo
  exact hN C (oneGenerated_of_irreducibles hCompleted C hPieces).1 hNo

theorem encoded_directObstruction {L : Signature.{u}} {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) {N : ℤ} (hN : DirectObstruction K N) :
    Native.RestrictedObstruction (EncodedClass K) N :=
  encoded_restrictedObstruction hCompleted (restricted_of_direct hCompleted hN)

def BinaryCoverage {L : Signature.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V : Type v} (C : Typed L V), K C → ∀ x y, x ≠ y → BinaryEdge C x y

/-- C40: retain the final source theorem's arity-at-most-two scope. Its
completed irreducibility premise is DERIVED from positive binary coverage. -/
theorem allIrreducible_of_binary {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : FiniteHereditarySAP K) (hCompleted : CompletedClass K)
    (_hArity : ∀ R : L.Rel, L.arity R ≤ 2) (hBinary : BinaryCoverage K) :
    AllIrreducible K := by
  intro V C hC
  let : Finite V := hK.finite C hC
  exact binary_coverage_irreducible C (hCompleted C hC) (hBinary C hC)

end CCO.UnaryHN.Raw
