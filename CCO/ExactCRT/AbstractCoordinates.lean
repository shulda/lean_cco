import CCO.ExactCRT.AbstractFibreProduct
import CCO.ExactCRT.FiniteOrder

/-! B008 C16 and boundary consumers: finite MI coordinates give actual
surjective maps of quotient SETS, with the prescribed projection formula. -/
namespace CCO.ExactCRT.Abstract
variable {A : Type*} (S : Sublattice (Setoid A))

/-- The coordinate carrying an actual MI quotient is selected by its
order inclusion, rather than any automorphism-lifting assertion. -/
theorem selected_coordinate_image (dist : Distributive S)
    (head : S) (tail : List S) (L : S)
    (hMI : FiniteOrder.BinaryMeetIrreducible L)
    (hle : FiniteOrder.listMeet head tail ≤ L) :
    ∃ J ∈ head :: tail, ∃ f : Quotient J.val → Quotient L.val,
      Function.Surjective f ∧ ∀ x, f (Quotient.mk _ x) = Quotient.mk _ x := by
  let : DistribLattice S := DistribLattice.ofInfSupLe dist
  obtain ⟨J, hJ, hJL⟩ := FiniteOrder.selected_meet_coordinate hMI head tail hle
  exact ⟨J, hJ, quotientMap hJL, quotientMap_surjective hJL, fun _ => rfl⟩

/-- The optional empty tuple has the AMBIENT top kernel, even if S
has no top member. Inhabitedness supplies its unique actual class. -/
theorem empty_coordinates_bijective [Nonempty A] :
    Function.Bijective (compatibleCoordinates (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Setoid A)) := by
  refine ⟨compatibleCoordinates_injective _, ?_⟩
  intro q
  obtain ⟨x⟩ := ‹Nonempty A›
  refine ⟨Quotient.mk _ x, ?_⟩
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- One represented quotient is unchanged by the natural coordinate map. -/
theorem one_coordinates_surjective (E : Setoid A) :
    Function.Surjective (compatibleCoordinates (fun _ : Fin 1 => E)) := by
  intro q
  induction h : q.val 0 using Quotient.inductionOn with
  | _ x =>
    refine ⟨Quotient.mk _ x, ?_⟩
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact h.symm

end CCO.ExactCRT.Abstract
