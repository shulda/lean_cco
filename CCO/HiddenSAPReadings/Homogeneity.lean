import CCO.HiddenSAPReadings.JointLift
import CCO.HereditaryHiddenOrbits.FullHidden
import CCO.UnaryFreshFrames.SAPAvoidance

/-! Hidden homogeneity is proved from original joint exact lifting before
the accepted hereditary orbit theorem is used for SAP. The domain is every
finite induced unary-closed piece, including orphan-only and empty pieces. -/
universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (nr2 : Selectors.OriginalNR2 S)

theorem closed_embeddings_pair_motion
    (A : (originalCompletedStructure S H sap nr2).Piece)
    (f g : A.Embedding Set.univ) (x y : A.points) :
    ∃ h : G, originalCompletedNamedAct S H h (f.point x) = g.point x ∧
      originalCompletedNamedAct S H h (f.point y) = g.point y := by
  classical
  by_cases hxy : x = y
  · subst y
    have hsort : originalCompletedVertexSort S H (f.point x) =
        originalCompletedVertexSort S H (g.point x) :=
      congrArg ULift.down ((f.sort_eq x).trans (g.sort_eq x).symm)
    obtain ⟨h,hh⟩ := same_sort_transitive S H (f.point x) (g.point x) hsort
    exact ⟨h,hh,hh⟩
  · obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap x.val y.val
      (fun h => hxy (Subtype.ext h))
    let xs : Fin ((originalCompletedLanguage S H sap nr2).arity R) → A.points := by
      change Fin 2 → A.points
      exact ![x,y]
    have hSource : (originalCompletedStructure S H sap nr2).rel R (Subtype.val ∘ xs) := hR
    exact same_binary_motion S H R ((f.rel_iff R xs).mpr hSource) ((g.rel_iff R xs).mpr hSource)

/-- Source13 C01–04: actual joint FULL-exact lifting and actual unary
enrichment, with no hidden homogeneity or SAP provider assumption. -/
theorem actual_hidden_homogeneous [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (originalCompletedStructure S H sap nr2).Homogeneous := by
  intro A f g
  let sort : A.points → OriginalCompletedCoordinateCode S H :=
    fun a => ((coordinateEquiv S H).symm (f.point a)).1
  let source : ∀ a, CoordinateValue S H (sort a) :=
    fun a => ((coordinateEquiv S H).symm (f.point a)).2
  have hsort (a : A.points) : originalCompletedVertexSort S H (f.point a) =
      originalCompletedVertexSort S H (g.point a) :=
    congrArg ULift.down ((f.sort_eq a).trans (g.sort_eq a).symm)
  let target : ∀ a, CoordinateValue S H (sort a) :=
    fun a => sameSortValue S H (f.point a) (g.point a) (hsort a)
  have hsource (a : A.points) : coordinateVertex S H (sort a) (source a) = f.point a :=
    (coordinateEquiv S H).apply_symm_apply _
  have htarget (a : A.points) : coordinateVertex S H (sort a) (target a) = g.point a :=
    sameSortValue_vertex S H _ _ _
  have hPairs (a b : A.points) : ∃ h : G,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort a))).act h
        (source a) = target a ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort b))).act h
        (source b) = target b := by
    obtain ⟨h,ha,hb⟩ := closed_embeddings_pair_motion S H sap nr2 A f g a b
    refine ⟨h,?_,?_⟩
    · apply coordinateVertex_injective S H (sort a)
      rw [coordinateVertex_equivariant,hsource,htarget]
      exact ha
    · apply coordinateVertex_injective S H (sort b)
      rw [coordinateVertex_equivariant,hsource,htarget]
      exact hb
  obtain ⟨e,hPair,hExt⟩ := finite_coordinate_family_lift S H cco nr2 sort source target hPairs
  refine ⟨coordinateAutomorphism S H sap nr2 e hPair,?_⟩
  intro a
  change coordinatePermutation S H e (f.point a) = g.point a
  rw [← hsource a,coordinatePermutation_vertex,hExt a,htarget]

/-- Source theorem: all standing providers are discharged before the
hereditary closed-age SAP criterion. FULL original cover infinitude derives
NR2; B054 gives full hidden stabilizer orbits by subgroup inclusion. -/
theorem typed_hidden_sap [∀ i, Countable (X i)]
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (CCO.HereditaryHiddenOrbits.hidden S H sap hCover).Homogeneous ∧
      (CCO.HereditaryHiddenOrbits.hidden S H sap hCover).LocallyFinite ∧
      (CCO.HereditaryHiddenOrbits.hidden S H sap hCover).AgeSAP := by
  have hom := actual_hidden_homogeneous S H sap
    (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover) cco
  exact ⟨hom,CCO.HereditaryHiddenOrbits.locally_finite S H sap hCover,
    Structure.ageSAP_of_infiniteClosedOrbits _ hom
      (CCO.HereditaryHiddenOrbits.full_closed_orbits S H sap hCover cco)⟩

end
end CCO.HiddenSAPReadings
