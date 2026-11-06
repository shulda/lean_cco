import CCO.HiddenSAPReadings.PairOrbitals
import CCO.TypedOrbitFrames.RealTermNormalForms
import CCO.TypedOrbitFrames.InfiniteCommonClass

/-! Source13 ACR: actual fine old spokes to a complete fixed frame retain
literal quotient classes, every nonidentity named term, and every retained
mixed cylinder. The argument is binary and uses no mixed-product commute. -/
universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

def SameFineToFrame {i : ι} (p p' : X i) (B : Set (Sigma X)) : Prop :=
  ∀ z ∈ B, S.colour p z.2 = S.colour p' z.2

/-- One actual anchor in the SAME quotient class pins that class. -/
theorem anchored_coordinate_eq {i : ι} (J : ColourEq S i)
    (p p' a : X i) (hJa : J p a) (hFine : S.colour p a = S.colour p' a) :
    Quotient.mk J.val p' = Quotient.mk J.val p := by
  have hJ' : J p' a := (J.property p a p' a hFine).mp hJa
  exact Quotient.sound (J.val.trans hJ' (J.val.symm hJa))

/-- A retained proper class can be represented in a DIFFERENT original
sort. The actual old pair motion fixes that class while moving p to p'. -/
theorem anchored_mixed_binary_iff {i j : ι} (p p' : X i)
    (D : OriginalNamedHiddenCoordinate S H j) (q : Quotient D.val.val)
    (a : X j) (ha : Quotient.mk D.val.val a = q)
    (hFine : S.colour p a = S.colour p' a)
    (R : OriginalCompletedCylinderBinaryName S H) :
    originalCompletedCylinderBinaryPredicate S H R (.inl ⟨i,p'⟩)
        (originalCompletedNamedHiddenNode S H D q) ↔
      originalCompletedCylinderBinaryPredicate S H R (.inl ⟨i,p⟩)
        (originalCompletedNamedHiddenNode S H D q) := by
  obtain ⟨g,hgp,hga⟩ := S.pair_homogeneous_of_homogeneous H p p' a a hFine
  have hFix : originalCompletedNamedAct S H g
      (originalCompletedNamedHiddenNode S H D q) =
        originalCompletedNamedHiddenNode S H D q := by
    rw [← ha]
    change originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val (g • a)) = _
    rw [hga]
  have h := original_completed_binary_equivariant S H g R
    (.inl ⟨i,p⟩) (originalCompletedNamedHiddenNode S H D q)
  rw [hFix] at h
  change originalCompletedCylinderBinaryPredicate S H R (.inl ⟨i,g • p⟩) _ ↔ _ at h
  rwa [hgp] at h

/-- The complete frame hypotheses are precisely the actual coordinate
and retained-vertex requests, not extra independent quotient choices. -/
structure AnchorFrame {i : ι} (p : X i) (Q : Set (OriginalCompletedNamedCarrier S H)) where
  points : Set (Sigma X)
  finite : points.Finite
  excludes : (⟨i,p⟩ : Sigma X) ∉ points
  coordinate : ∀ D : OriginalNamedHiddenCoordinate S H i,
    ∃ a : X i, (⟨i,a⟩ : Sigma X) ∈ points ∧ D.val p a
  retained : ∀ {j : ι} (D : OriginalNamedHiddenCoordinate S H j)
    (q : Quotient D.val.val), originalCompletedNamedHiddenNode S H D q ∈ Q →
    ∃ a : X j, (⟨j,a⟩ : Sigma X) ∈ points ∧ Quotient.mk D.val.val a = q

theorem anchored_all_coordinates {i : ι} (p p' : X i)
    {Q : Set (OriginalCompletedNamedCarrier S H)} (B : AnchorFrame S H p Q)
    (hFine : SameFineToFrame S p p' B.points) :
    ∀ D : OriginalNamedHiddenCoordinate S H i,
      Quotient.mk D.val.val p' = Quotient.mk D.val.val p := by
  intro D
  obtain ⟨a,ha,hJa⟩ := B.coordinate D
  exact anchored_coordinate_eq S D.val p p' a hJa (hFine ⟨i,a⟩ ha)

/-- Every nonidentity actual real-source term factors through an existing
represented coordinate. The real identity term is deliberately excluded. -/
theorem anchored_nonidentity_term_values (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι} (p p' : X i)
    (hCoordinates : ∀ D : OriginalNamedHiddenCoordinate S H i,
      Quotient.mk D.val.val p' = Quotient.mk D.val.val p)
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (hNonId : C ≠ ⟨⟨i,.inl ()⟩⟩) :
    (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,p'⟩) =
      (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,p⟩) := by
  rcases original_real_term_literal_named_form S H sap nr2 t with
    ⟨hC,_⟩ | ⟨j,D,E,s,_,hVal⟩
  · exact False.elim (hNonId hC)
  · rw [hVal p',hVal p,hCoordinates D]

/-- Source ACR, retaining all named functions and all mixed readings on
the SAME actual proper quotient vertices, including mixed original sorts. -/
theorem typed_anchored_real_clone_readout (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι} (p p' : X i)
    {Q : Set (OriginalCompletedNamedCarrier S H)} (B : AnchorFrame S H p Q)
    (hFine : SameFineToFrame S p p' B.points) :
    (∀ D : OriginalNamedHiddenCoordinate S H i,
      Quotient.mk D.val.val p' = Quotient.mk D.val.val p) ∧
    (∀ {C : (originalCompletedLanguage S H sap nr2).Sorts}
      (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C),
      C ≠ ⟨⟨i,.inl ()⟩⟩ →
      (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,p'⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,p⟩)) ∧
    (∀ {j : ι} (D : OriginalNamedHiddenCoordinate S H j) (q : Quotient D.val.val),
      originalCompletedNamedHiddenNode S H D q ∈ Q →
      ∀ R : OriginalCompletedCylinderBinaryName S H,
        originalCompletedCylinderBinaryPredicate S H R (.inl ⟨i,p'⟩)
            (originalCompletedNamedHiddenNode S H D q) ↔
          originalCompletedCylinderBinaryPredicate S H R (.inl ⟨i,p⟩)
            (originalCompletedNamedHiddenNode S H D q)) := by
  have hc := anchored_all_coordinates S H p p' B hFine
  refine ⟨hc,fun t ht => anchored_nonidentity_term_values S H sap nr2 p p' hc t ht,?_⟩
  intro j D q hq R
  obtain ⟨a,ha,hrep⟩ := B.retained D q hq
  exact anchored_mixed_binary_iff S H p p' D q a hrep (hFine ⟨j,a⟩ ha) R

end
end CCO.HiddenSAPReadings
