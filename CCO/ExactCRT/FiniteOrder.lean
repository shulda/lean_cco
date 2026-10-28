import Mathlib.Order.Birkhoff
import Mathlib.Data.List.Fold

/-! Finite order arguments for B008 C08–10 and C15. `SupIrred` excludes
bottom; the downsets are the actual downsets of those nonzero elements.
The matching library Birkhoff proof is reused with its explicit maps. -/

namespace CCO.ExactCRT.FiniteOrder

variable {L : Type*} [DistribLattice L]

/-- C08, including the nonzero convention when a bottom is present. -/
theorem join_irreducible_prime {p x y : L} (hp : SupIrred p) :
    p ≤ x ⊔ y ↔ p ≤ x ∨ p ≤ y := hp.supPrime.le_sup

theorem join_irreducible_finite_prime [OrderBot L] {I : Type*}
    (s : Finset I) (f : I → L) {p : L} (hp : SupIrred p) :
    p ≤ s.sup f ↔ ∃ i ∈ s, p ≤ f i := hp.supPrime.le_finset_sup

/-- C09: actual finite decomposition, with bottom the empty join. -/
theorem irreducible_decomposition [OrderBot L] [Finite L] (a : L) :
    ∃ s : Finset L, s.sup id = a ∧ ∀ p ∈ s, SupIrred p := by
  obtain ⟨s, h, hs⟩ := exists_supIrred_decomposition a
  exact ⟨s, h, fun _ hp => hs hp⟩

abbrev JoinIrreducible (L : Type*) [SemilatticeSup L] := {p : L // SupIrred p}

theorem joinIrreducible_ne_bot [OrderBot L] (p : JoinIrreducible L) :
    p.val ≠ ⊥ := p.property.ne_bot

/-- C10: finite Birkhoff, with the literal source forward and inverse maps. -/
noncomputable def birkhoff [OrderBot L] [Finite L] :
    L ≃o LowerSet (JoinIrreducible L) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  exact OrderIso.lowerSetSupIrred

@[simp] theorem mem_birkhoff [OrderBot L] [Finite L] (a : L)
    (p : JoinIrreducible L) : p ∈ birkhoff a ↔ p.val ≤ a := Iff.rfl

noncomputable def downJoin [OrderBot L] [Finite L]
    (D : LowerSet (JoinIrreducible L)) : L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  exact (D : Set (JoinIrreducible L)).toFinset.sup Subtype.val

@[simp] theorem birkhoff_inverse [OrderBot L] [Finite L]
    (D : LowerSet (JoinIrreducible L)) :
    (birkhoff (L := L)).symm D =
      downJoin D := by
  classical
  rfl

/-- Binary meet-irreducibility, retaining the source nonempty-family
convention even if a binary convention admits top. -/
def BinaryMeetIrreducible {M : Type*} [SemilatticeInf M] (p : M) : Prop :=
  ∀ x y, x ⊓ y = p → x = p ∨ y = p

/-- C15's local distributive calculation. -/
theorem binary_meet_irreducible_prime {p x y : L}
    (hp : BinaryMeetIrreducible p) (h : x ⊓ y ≤ p) : x ≤ p ∨ y ≤ p := by
  have heq : (x ⊔ p) ⊓ (y ⊔ p) = p := by
    rw [← sup_inf_right, sup_eq_right.mpr h]
  exact (hp _ _ heq).imp (fun hx => le_sup_left.trans_eq hx)
    (fun hy => le_sup_left.trans_eq hy)

/-- A nonempty-list meet avoids introducing a top assumption. -/
def listMeet {M : Type*} [SemilatticeInf M] (head : M) : List M → M
  | [] => head
  | x :: xs => head ⊓ listMeet x xs

/-- Selected coordinates may repeat and need not themselves be MI. -/
theorem selected_meet_coordinate {p : L} (hp : BinaryMeetIrreducible p)
    (head : L) (tail : List L) (h : listMeet head tail ≤ p) :
    ∃ x ∈ head :: tail, x ≤ p := by
  induction tail generalizing head with
  | nil => exact ⟨head, by simp, h⟩
  | cons x xs ih =>
    obtain hh | ht := binary_meet_irreducible_prime hp h
    · exact ⟨head, by simp, hh⟩
    · obtain ⟨y, hy, hyp⟩ := ih x ht
      exact ⟨y, by simp only [List.mem_cons] at hy ⊢; exact Or.inr hy, hyp⟩

theorem selected_meet_coordinate_of_infIrred {p : L} (hp : InfIrred p)
    (head : L) (tail : List L) (h : listMeet head tail ≤ p) :
    ∃ x ∈ head :: tail, x ≤ p :=
  selected_meet_coordinate (fun _ _ hxy => hp.2 hxy) head tail h

/-- The one-element boundary has no nonzero join-irreducibles. -/
theorem no_irreducibles_of_subsingleton [OrderBot L] [Subsingleton L] :
    IsEmpty (JoinIrreducible L) :=
  ⟨fun p => p.property.ne_bot (Subsingleton.elim _ _)⟩

end CCO.ExactCRT.FiniteOrder
