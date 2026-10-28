import CCO.RealClosure.Bounds.Examples.CoordinateLattice
import CCO.RealClosure.Bounds.Directions

/-! Actual finite packets and minimal infinite directions in the coordinate
source. Nonempty coordinate-change classes contain Nat, not finite snapshots. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
open ParityHasse.Original
variable (I : Type u) [Fintype I] [DecidableEq I]

@[simp] theorem changeEq_empty : changeEq I ∅ = (⊥ : ColourEq (source I) ()) := by
  apply ColourEq.ext
  intro x y
  change (∀ i, i ∉ (∅ : Finset I) → x i = y i) ↔ x = y
  exact ⟨fun h => funext (fun i => h i (Finset.notMem_empty i)),fun h i _ => congrFun h i⟩

theorem finite_change_iff (J : Finset I) : FiniteClasses (source I) (changeEq I J) ↔ J = ∅ := by
  classical
  constructor
  · intro hf
    by_contra hn
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    letI := hf (fun _ => 0)
    have hnat : Finite ℕ := Finite.of_injective (classNatEmbedding I hi (fun _ => 0))
      (classNatEmbedding I hi (fun _ => 0)).injective
    letI := hnat
    exact not_finite ℕ
  · rintro rfl
    rw [changeEq_empty]
    exact finiteClasses_bot (source I)

theorem finite_equivalence_iff_bot (E : ColourEq (source I) ()) :
    FiniteClasses (source I) E ↔ E = ⊥ := by
  rw [← full_equivalence_classification I E,finite_change_iff]
  constructor
  · intro h; rw [h,changeEq_empty]
  · intro he
    have hh := congrArg (allowedCoords I) he
    simpa only [allowed_change,← changeEq_empty I,allowed_change] using hh

@[simp] theorem finitePacket_identity :
    finitePacket (source I) (homogeneous I) = ⊥ :=
  (finite_equivalence_iff_bot I _).mp (finitePacket_finite (source I) (homogeneous I))

theorem direction_change_iff (J : Finset I) :
    IsDirection (source I) (changeEq I J) ↔ ∃ i : I, J = {i} := by
  classical
  constructor
  · rintro ⟨hinf,hmin⟩
    have hJ : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun he => hinf ((finite_change_iff I J).mpr he))
    obtain ⟨i,hi⟩ := hJ
    refine ⟨i,?_⟩
    apply Finset.Subset.antisymm
    · intro j hj
      by_contra hji
      have hneq : ({i} : Finset I) ≠ J := by
        intro he
        rw [← he] at hj
        exact hji hj
      have hlt : changeEq I {i} < changeEq I J := by
        apply lt_of_le_of_ne
        · exact (changeEq_le_iff I _ _).mpr (Finset.singleton_subset_iff.mpr hi)
        · intro he
          exact hneq (congrArg (allowedCoords I) he |>.trans (allowed_change I J) |>
            (allowed_change I {i}).symm.trans)
      have hfin := (finite_change_iff I {i}).mp (hmin _ hlt)
      exact Finset.singleton_ne_empty i hfin
    · exact Finset.singleton_subset_iff.mpr hi
  · rintro ⟨i,rfl⟩
    refine ⟨fun h => Finset.singleton_ne_empty i ((finite_change_iff I {i}).mp h),?_⟩
    intro E hE
    rw [← full_equivalence_classification I E] at hE ⊢
    have hsub : allowedCoords I E ⊆ {i} := (changeEq_le_iff I _ _).mp hE.le
    apply (finite_change_iff I _).mpr
    by_contra hn
    obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    have hji : j = i := Finset.mem_singleton.mp (hsub hj)
    have he : allowedCoords I E = {i} := Finset.Subset.antisymm hsub
      (Finset.singleton_subset_iff.mpr (hji ▸ hj))
    rw [he] at hE
    exact lt_irrefl _ hE

noncomputable def directionsEquiv : I ≃ Direction (source I) where
  toFun i := ⟨changeEq I {i},(direction_change_iff I {i}).mpr ⟨i,rfl⟩⟩
  invFun E := Classical.choose ((direction_change_iff I (allowedCoords I E.val)).mp
    (by simpa only [full_equivalence_classification] using E.property))
  left_inv i := by
    apply Finset.singleton_injective
    exact (Classical.choose_spec ((direction_change_iff I (allowedCoords I (changeEq I {i}))).mp
      (by simpa only [full_equivalence_classification] using
        (direction_change_iff I {i}).mpr ⟨i,rfl⟩))).symm.trans (allowed_change I {i})
  right_inv E := by
    apply Subtype.ext
    have hh := Classical.choose_spec ((direction_change_iff I (allowedCoords I E.val)).mp
      (by simpa only [full_equivalence_classification] using E.property))
    exact (congrArg (changeEq I) hh.symm).trans (full_equivalence_classification I E.val)

theorem direction_count : directionCount (source I) = Nat.card I :=
  (Nat.card_congr (directionsEquiv I)).symm

theorem diversity_atom_count : Nat.card (Colour I) = 2^(Nat.card I) - 1 := by
  classical
  let e : Option (Colour I) ≃ Finset I := {
    toFun := fun a => match a with | none => ∅ | some a => a.val
    invFun := fun J => if h : J.Nonempty then some ⟨J,h⟩ else none
    left_inv := by intro a; cases a with
      | none => simp
      | some a => simp [a.property]
    right_inv := by
      intro J
      dsimp only
      split_ifs with h
      · rfl
      · exact (Finset.not_nonempty_iff_eq_empty.mp h).symm
  }
  have hh := Nat.card_congr e
  simp only [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_finset] at hh ⊢
  omega
end CCO.RealClosure.Bounds.Examples.Coordinate
