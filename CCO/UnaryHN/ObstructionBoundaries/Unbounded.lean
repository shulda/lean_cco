import CCO.UnaryHN.ObstructionBoundaries.ProperCompletion
import CCO.UnaryHN.Obstruction
import CCO.UnaryHN.UnaryFunctions

/-! Every integer cutoff fails on a concrete finite path-with-chord source.
The obstruction is minimal among ALL actual induced subsets, and its actual
one-generated structures already belong to the completed class. -/

namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

theorem path_singleton_hull_completed {n : ℕ} (hn : 4 ≤ n) (x : Fin n) :
    completed ((path n).induce
      ((path n).functionClosure (Set.range (fun _ : PUnit.{1} => x)))
      ((path n).functionClosure_isClosed (Set.range (fun _ : PUnit.{1} => x)))) :=
  path_irreducibles_completed hn _ (one_point_hull_irreducible (path n) x)
    (inclusion _ _ _)

/-- There is no integer N supplying the source's restricted obstruction
bound, even though every protected irreducible is an actual K-member. -/
theorem no_uniform_obstruction_bound (N : ℤ) : ¬ RestrictedObstruction (completed.{0}) N := by
  intro hBound
  let n : ℕ := N.toNat + 4
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hLarge : N < (n : ℤ) := by dsimp [n]; omega
  obtain ⟨S, hS, hSize, hBad⟩ := hBound (path n) (singleton _)
    (path_irreducibles_completed hn) (path_no_completion (n := n) (by omega))
  have hProper : (↑S : Set (Fin n)) ≠ Set.univ := by
    intro hEq
    have hUniv : S = Finset.univ := by
      ext x
      change x ∈ (↑S : Set (Fin n)) ↔ x ∈ (Finset.univ : Finset (Fin n))
      simp only [hEq, Set.mem_univ, Finset.mem_univ]
    have hCard : S.card = n := by rw [hUniv, Finset.card_univ, Fintype.card_fin]
    omega
  exact hBad (every_proper_subset_completes hn (↑S : Set (Fin n)) hProper).to_completion

end CCO.UnaryHN.Native.ObstructionBoundaries
