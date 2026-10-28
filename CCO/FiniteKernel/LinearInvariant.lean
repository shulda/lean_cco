import CCO.FiniteKernel.LinearSource
import CCO.FiniteKernel.RestrictedRows

/-! Source C13–15 on the ACTUAL full original owner kernel. Every finite and
countability instance is derived from the actual finite fibres and intrinsic
group representations; no owner homogeneity or finite-projection equality is
assumed. Singleton actual binding constraints remain part of width two.
-/

universe u v w z t
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I) (V : I → Type t)
variable [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

include P e in
theorem coordinate_dual_finite (i : I) : Finite (Module.Dual F2 (V i)) := by
  classical
  letI : Finite (V i) := P.coordinate_finite V e i
  letI : Fintype (V i) := Fintype.ofFinite _
  apply Finite.of_injective (fun phi : Module.Dual F2 (V i) => (phi : V i → F2))
  exact DFunLike.coe_injective

include P e in
theorem source_tests_countable [Countable X] [DecidableEq I] :
    Countable (TestSpace F2 V) := by
  letI : Countable I := P.countable_owners
  letI : ∀ i,Finite (Module.Dual F2 (V i)) := P.coordinate_dual_finite V e
  letI : ∀ i,Countable (Module.Dual F2 (V i)) := fun _ => inferInstance
  change Countable (Π₀ i,Module.Dual F2 (V i))
  infer_instance

theorem source_double_annihilator [Countable X] [DecidableEq I] :
    ann F2 V (P.linearKernel V e) = pairRows F2 V (P.localPairSpace V e) := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  letI : Countable (TestSpace F2 V) := P.source_tests_countable V e
  rw [P.linearKernel_eq_perp,ann_perp]

theorem source_restricted_annihilator [Countable X] [DecidableEq I] (A : Finset I) :
    (finiteProjection F2 V (P.linearKernel V e) A).dualAnnihilator.map (extendForm F2 V A) =
      pairRows F2 V (P.localPairSpace V e) ⊓ restrictedTestSpace F2 V A := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  letI : Countable (TestSpace F2 V) := P.source_tests_countable V e
  rw [P.linearKernel_eq_perp]
  exact restricted_annihilator_map F2 V _ A

theorem source_marginal_annihilator [Countable X] [DecidableEq I] (A : Finset I) :
    (marginalSpace F2 V (P.linearKernel V e) A).dualAnnihilator.map (extendForm F2 V A) =
      marginalRows F2 V (pairRows F2 V (P.localPairSpace V e)) A := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  letI : Countable (TestSpace F2 V) := P.source_tests_countable V e
  rw [P.linearKernel_eq_perp]
  exact marginal_annihilator_map F2 V _ A

theorem source_width_two [Countable X] [DecidableEq I] (A : Finset I) :
    finiteProjection F2 V (P.linearKernel V e) A = marginalSpace F2 V (P.linearKernel V e) A ↔
      pairRows F2 V (P.localPairSpace V e) ⊓ restrictedTestSpace F2 V A =
        marginalRows F2 V (pairRows F2 V (P.localPairSpace V e)) A := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  letI : Countable (TestSpace F2 V) := P.source_tests_countable V e
  rw [P.linearKernel_eq_perp]
  exact width_two_iff F2 V _ A

end
end CCO.FiniteKernel.FinitePartition
