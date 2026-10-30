import CCO.FiniteFibres.FiniteAtomic
import CCO.FiniteFibres.SourceChain
import CCO.FiniteFibres.Real.Source

/-! Discharge the actual finite-fibre/real-closure theorem. Its finite target
cardinal support is the proved theorem, not a constructor field or callback
assumed from a source or a later Hasse theorem. -/
universe v w t
namespace CCO.FiniteFibres

theorem finiteCard_provider : Real.FiniteAtomicCard.{v,w} := by
  intro F T _ _ K _ _ H cco
  have h := actual_source_chain_bounds T H cco
  exact ⟨(sourceSaturatedChain T).length,h⟩

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : CCO.SemanticCCO.{0,v,0,w} S)
include H cco

/-- `cor:fibre-uniform-acl`, with the actual full original stabilizer
orbits and ordinary first-order algebraicity connected in the conclusion.
No SAP, countability, triangle-fullness or imaginary-fibre premise occurs. -/
theorem actual_real_fibre_bounds (A : Finset M) :
    (∀ q : ↥A → S.Atom () (),
      ∀ [Nonempty (RealHull.Geometry.FibreSet S A q)] [Finite (RealHull.Geometry.FibreSet S A q)],
      ∃ m : Nat, Nat.card (RealHull.Geometry.FibreSet S A q) = 2^m ∧
        m ≤ Nat.card (S.Atom () ())) ∧
    (Real.acl S A).Finite ∧
    (A.Nonempty → Nat.card ↥(Real.acl S A) ≤
      A.card + (Nat.card (S.Atom () ())) ^ A.card * 2 ^ Nat.card (S.Atom () ())) ∧
    (∀ [Infinite M], Real.acl S ∅ = ∅) ∧
    (∀ [Finite M], Real.acl S ∅ = Set.univ ∧
      ∃ m : Nat, Nat.card M = 2^m ∧ m ≤ Nat.card (S.Atom () ()) ∧
        Nat.card M ≤ 2 ^ Nat.card (S.Atom () ())) ∧
    (∀ x : M, (∃ Z : Set M, Z.Finite ∧
      (A : Set M).Definable₁ (Real.originalLanguage S) Z ∧ x ∈ Z) ↔ x ∈ Real.acl S A) :=
  Real.real_source_package S H cco finiteCard_provider A

end CCO.FiniteFibres
