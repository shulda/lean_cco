import CCO.FiniteKernel.ActualMarginals
import CCO.FiniteKernel.ActualPartition
import CCO.FiniteKernel.F2Subgroup
import CCO.FiniteKernel.PairRows
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Field.ZMod

/-! Actual intrinsic elementary-abelian coordinates of the full owner kernel.
The local spaces are the genuine intrinsic H_CD pullbacks, including
nonsubdirect groups. Pair rows are therefore all and ONLY valid local tests.
-/

universe u v w z t
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I) (V : I → Type t)
variable [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

include P e in
theorem coordinate_finite (i : I) : Finite (V i) := by
  apply Finite.of_injective (fun x : V i => e i (Multiplicative.ofAdd x))
  intro a b hab
  exact congrArg Multiplicative.toAdd ((e i).injective hab)

def localPairSpace (i j : I) : Submodule F2 (V i × V j) :=
  F2Subgroup.linearPreimage (F2Subgroup.pairRepresentation (e i) (e j)).toMonoidHom (P.pairGroup i j)

def linearKernel : Submodule F2 (∀ i,V i) :=
  F2Subgroup.linearPreimage (F2Subgroup.tupleRepresentation e).toMonoidHom P.rho.range

theorem linearKernel_eq_constraints : P.linearKernel V e = pairConstraints F2 V (P.localPairSpace V e) := by
  ext x
  change (fun i => e i (Multiplicative.ofAdd (x i))) ∈ Set.range P.rho ↔ _
  exact P.mem_range_rho _

/-- C10 actual source representation, with finiteness/finite dimension of
the vector coordinates DERIVED from their intrinsic-group isomorphisms. -/
theorem linearKernel_eq_perp [DecidableEq I] :
    P.linearKernel V e = perp F2 V (pairRows F2 V (P.localPairSpace V e)) := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  rw [perp_pairRows,P.linearKernel_eq_constraints V e]

theorem actual_motion_iff [DecidableEq I] (x : ∀ i,V i) :
    x ∈ perp F2 V (pairRows F2 V (P.localPairSpace V e)) ↔
      ∃ n : P.kernel, ∀ i,P.restrictFibre i n = e i (Multiplicative.ofAdd (x i)) := by
  rw [← P.linearKernel_eq_perp V e]
  change (fun i => e i (Multiplicative.ofAdd (x i))) ∈ Set.range P.rho ↔ _
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,fun i => congrFun hn i⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,funext hn⟩

/-- The defining rows for one isolated intrinsic coordinate are zero. -/
theorem rows_single_owner [DecidableEq I] [Subsingleton I] :
    pairRows F2 V (P.localPairSpace V e) = ⊥ := by
  letI : ∀ i,Finite (V i) := P.coordinate_finite V e
  letI : ∀ i,FiniteDimensional F2 (V i) := fun _ => inferInstance
  exact pairRows_of_subsingleton F2 V _

end
end CCO.FiniteKernel.FinitePartition
