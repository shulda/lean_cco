import CCO.HereditaryHiddenOrbits.Transfer

/-!
# Full hidden orbit closures, by subgroup inclusion

Original motions embed into full hidden Aut. The needed orbit inclusion is
from the original orbit INTO the full orbit. Named term values are fixed
by every full hidden automorphism, so the converse closure inclusion is
also proved without identifying the groups or assuming hidden homogeneity.
-/

universe u v w r
namespace CCO.HereditaryHiddenOrbits
open CCO.ParityHasse.Original CCO.UnaryFreshFrames CCO.TypedOrbitFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

/-- C17: original parameter fixers act as full hidden parameter fixers.
Only this direction of orbit inclusion is needed. -/
theorem original_orbit_subset_full (T : Set (Carrier S H)) (x : Carrier S H) :
    OriginalOrbit S H T x ⊆ orbitOver (hidden S H sap hCover).Aut T x := by
  rintro y ⟨g,hFix,hMove⟩
  apply (mem_orbitOver_iff _).mpr
  exact ⟨originalCompletedMotionHom S H sap (terminalNR2 S hCover) g,hFix,hMove⟩

theorem full_closed_orbits
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (hidden S H sap hCover).InfiniteClosedOrbits (hidden S H sap hCover).Aut := by
  intro A hA hClosed x hx
  exact (original_hidden_closed_orbit_infinite S H sap hCover cco A hA hClosed x hx).mono
    (original_orbit_subset_full S H sap hCover A x)

/-- C04/C19 for the ENTIRE full group, with pointwise stabilizers. -/
theorem full_fixer_closure_eq (T : Set (Carrier S H)) :
    fixer (hidden S H sap hCover).Aut ((hidden S H sap hCover).closure T) =
      fixer (hidden S H sap hCover).Aut T := by
  ext g
  constructor
  · intro hg x hx
    exact hg x ((hidden S H sap hCover).subset_closure T hx)
  · intro hg
    exact (hidden S H sap hCover).closure_fixed g hg

theorem full_orbit_closure_eq (T : Set (Carrier S H)) (x : Carrier S H) :
    orbitOver (hidden S H sap hCover).Aut ((hidden S H sap hCover).closure T) x =
      orbitOver (hidden S H sap hCover).Aut T x := by
  unfold orbitOver
  rw [full_fixer_closure_eq S H sap hCover]

/-- C18: outside the finite term hull, the full hidden orbit is infinite;
the larger group cannot make an infinite original orbit finite. -/
theorem full_off_hull_orbit_infinite
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite)
    (x : Carrier S H) (hx : x ∉ (hidden S H sap hCover).closure T) :
    (orbitOver (hidden S H sap hCover).Aut T x).Infinite := by
  have hi := full_closed_orbits S H sap hCover cco
    ((hidden S H sap hCover).closure T)
    (locally_finite S H sap hCover T hT)
    ((hidden S H sap hCover).closure_closed T) x hx
  rwa [full_orbit_closure_eq S H sap hCover] at hi

/-- Every named term value is fixed by EVERY full hidden automorphism
fixing its original parameter, independently of original-group surjectivity. -/
theorem term_hull_subset_full_dcl (T : Set (Carrier S H)) :
    (hidden S H sap hCover).closure T ⊆ Dcl (hidden S H sap hCover).Aut T := by
  intro x hx g
  exact (hidden S H sap hCover).closure_fixed g.val g.property x hx

/-- Orbit-theoretic algebraic closure for FULL hidden Aut. -/
theorem full_acl_eq_closure
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite) :
    Acl (hidden S H sap hCover).Aut T = (hidden S H sap hCover).closure T := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    exact full_off_hull_orbit_infinite S H sap hCover cco T hT x hnot hx
  · exact (term_hull_subset_full_dcl S H sap hCover T).trans
      (dcl_subset_acl _ T)

/-- Orbit-theoretic definable closure for FULL hidden Aut. -/
theorem full_dcl_eq_closure
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite) :
    Dcl (hidden S H sap hCover).Aut T = (hidden S H sap hCover).closure T := by
  apply Set.Subset.antisymm
  · exact (dcl_subset_acl _ T).trans
      (by rw [full_acl_eq_closure S H sap hCover cco T hT])
  · exact term_hull_subset_full_dcl S H sap hCover T

/-- The literal empty case needs no chosen representative or constant. -/
theorem empty_parameter_closures
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (hidden S H sap hCover).closure ∅ = ∅ ∧
      Acl (hidden S H sap hCover).Aut (∅ : Set (Carrier S H)) = ∅ ∧
      Dcl (hidden S H sap hCover).Aut (∅ : Set (Carrier S H)) = ∅ := by
  rw [full_acl_eq_closure S H sap hCover cco ∅ Set.finite_empty,
    full_dcl_eq_closure S H sap hCover cco ∅ Set.finite_empty,
    (hidden S H sap hCover).closure_empty]
  exact ⟨rfl,rfl,rfl⟩

end
end CCO.HereditaryHiddenOrbits
