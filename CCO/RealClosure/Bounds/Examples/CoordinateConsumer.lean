import CCO.RealClosure.Bounds.Examples.CoordinateCCO
import CCO.RealClosure.Bounds.Examples.CoordinateNonSAP

/-! C17–18 on the actual infinite family Nat^r, with every provider discharged.
The palette-cost and polynomial exponent equalities are literal sharpness
statements about full automorphisms and real closures. -/
universe z
namespace CCO.RealClosure.Bounds.Examples.Coordinate

theorem infinite_coordinate_source (r : ℕ) (hr : 2 ≤ r) :
    Infinite (Point (Fin r)) := by
  have hpos : 0 < r := by omega
  letI : Nonempty (Fin r) := ⟨⟨0,hpos⟩⟩
  exact Infinite.of_injective (fun n : ℕ => (fun _ : Fin r => n))
    (fun n m he => congrFun he ⟨0,hpos⟩)

theorem coordinate_sharpness_source (r : ℕ) (hr : 2 ≤ r) :
    HomogeneousSource (source (Fin r)) (Aut (Fin r)) ∧
    AgeAP (source (Fin r)) ∧ SemanticCCO.{0,0,z,0} (source (Fin r)) ∧
    finitePacket (source (Fin r)) (homogeneous (Fin r)) = ⊥ ∧
    directionCount (source (Fin r)) = r ∧
    Nat.card (Colour (Fin r)) = 2^r-1 ∧
    (∀ A : Finset (Point (Fin r)), Acl (Aut (Fin r)) A = grid (Fin r) A ∧
      Dcl (Aut (Fin r)) A = grid (Fin r) A) ∧
    (∀ n : ℕ, Nat.card (Acl (Aut (Fin r)) (diagonal (Fin r) n)) = n^r ∧
      Nat.card (Dcl (Aut (Fin r)) (diagonal (Fin r) n)) = n^r) ∧
    ¬ AgeSAP (source (Fin r)) := by
  refine ⟨homogeneous _,ageAP _,semanticCCO _,finitePacket_identity _,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.card_fin] using direction_count (Fin r)
  · simpa only [Nat.card_fin] using diversity_atom_count (Fin r)
  · exact fun A => ⟨acl_eq_grid _ A,dcl_eq_grid _ A⟩
  · intro n
    simpa only [Nat.card_fin] using diagonal_closure_card (Fin r) n
  · let i : Fin r := ⟨0,by omega⟩
    let j : Fin r := ⟨1,by omega⟩
    exact notSAP_of_two_coordinates (Fin r) (i := i) (j := j)
      (fun he => by have hh := congrArg Fin.val he; simp [i,j] at hh)
end CCO.RealClosure.Bounds.Examples.Coordinate
