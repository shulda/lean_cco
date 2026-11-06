import CCO.ExactEPGeometry.TypeSupport

/-!
# B062 C110: finite genuine type-support counterexample to empty meets

The source finite-type-support map Phi is existential over actual old
points. Even with ONE realized current unary type containing two
distinct real clone points, an old real logical diagonal and the
diversity relation on these two points are disjoint as OLD binary
relations. Nevertheless BOTH occupy the same actual current type
loop. Thus an empty old meet cannot be transported as the meet of
images without the source C47 nonempty-intersection hypothesis.

The two-point control is semantic and exact (real equality vs actual
inequality), not an axiom, an invented equality-diversity atom, or a
proof of the much stronger arbitrary-prefix marked-age claims.
-/

namespace CCO.ExactEPGeometry

private def clonedOneType : Bool → Unit := fun _ => ()

private def cloneOldIdentity : Bool → Bool → Prop :=
  fun x y => x = y

private def cloneOldDiversity : Bool → Bool → Prop :=
  fun x y => x ≠ y

/-- The two ACTUAL old point-relations are disjoint on every pair. -/
theorem originalC110_disjointOldIdentityDiversity :
    ∀ x y : Bool, ¬(cloneOldIdentity x y ∧ cloneOldDiversity x y) := by
  intro x y h
  exact h.2 h.1

/-- Old logical identity occurs as a genuine pair inside the sole type. -/
theorem originalC110_oldIdentityHasTypeLoop :
    typeSupport clonedOneType cloneOldIdentity () () := by
  exact ⟨false,false,rfl,rfl,rfl⟩

/-- Old diversity ALSO occurs on that very same current type loop,
witnessed by two different real points, not a fictitious diagonal. -/
theorem originalC110_oldDiversityHasSameTypeLoop :
    typeSupport clonedOneType cloneOldDiversity () () := by
  refine ⟨false,true,rfl,rfl,?_⟩
  change false ≠ true
  decide

/-- C110: finite type support cannot preserve this empty old meet:
Phi(Id) and Phi(Diversity) overlap on the actual unique type loop,
although Phi(Id intersect Diversity) is empty there. -/
theorem originalC110_emptyOldMeetNotPreserved :
    typeSupport clonedOneType cloneOldIdentity () () ∧
      typeSupport clonedOneType cloneOldDiversity () () ∧
      ¬ typeSupport clonedOneType
        (fun x y => cloneOldIdentity x y ∧ cloneOldDiversity x y) () () := by
  refine ⟨originalC110_oldIdentityHasTypeLoop,
    originalC110_oldDiversityHasSameTypeLoop,?_⟩
  rintro ⟨x,y,_,_,hxy⟩
  exact originalC110_disjointOldIdentityDiversity x y hxy

end CCO.ExactEPGeometry
