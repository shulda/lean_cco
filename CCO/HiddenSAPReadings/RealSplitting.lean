import CCO.HiddenSAPReadings.SplittingFrames

/-! Actual binary representative splitting in one old homogeneous SAP
source. Every retained quotient position and every real-root proper
coordinate receives a distinct fixed anchor BEFORE any real splitting.
Existing quotient values are literal and are never split or reassigned. -/
universe u v w r z t
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
/-- Concrete finite-family form of source representative splitting. The
root/quotient families may include repeated images, and orphan requests
need no real generator in the source. The visible target remains literal. -/
theorem typed_real_sort_splitting {I : Type z} [Finite I]
    {J : Type t} [Finite J] (sort : I → ι) (old : ∀ i, X (sort i))
    (q : J → AnchorRequest S H) (A : Set (Sigma X)) (hA : A.Finite) :
    ∃ (fresh : ∀ i, X (sort i)) (anchor : J → Sigma X) (A' : FiniteInduced (X := X)),
      A ⊆ A'.vertices ∧
      Function.Injective (fun i => (⟨sort i,fresh i⟩ : Sigma X)) ∧
      Function.Injective anchor ∧
      (∀ j, anchor j ∈ anchorRepresentatives S H (q j)) ∧
      (∀ i j, (⟨sort i,fresh i⟩ : Sigma X) ≠ anchor j) ∧
      (∀ i, (⟨sort i,fresh i⟩ : Sigma X) ∈ A'.vertices) ∧
      (∀ j, anchor j ∈ A'.vertices) ∧
      (∀ i (D : OriginalNamedHiddenCoordinate S H (sort i)),
        Quotient.mk D.val.val (fresh i) = Quotient.mk D.val.val (old i)) ∧
      (∀ i j (a : S.Atom (sort i) (sort j)), S.atomRel a (old i) (old j) →
        S.atomRel a (fresh i) (fresh j)) ∧
      (∀ i j (R : OriginalCompletedCylinderBinaryName S H),
        originalCompletedCylinderBinaryPredicate S H R (.inl ⟨sort i,fresh i⟩)
            (originalCompletedNamedHiddenNode S H (q j).2.1 (q j).2.2) ↔
          originalCompletedCylinderBinaryPredicate S H R (.inl ⟨sort i,old i⟩)
            (originalCompletedNamedHiddenNode S H (q j).2.1 (q j).2.2)) := by
  classical
  letI (i : I) : Finite (OriginalNamedHiddenCoordinate S H (sort i)) :=
    original_named_hidden_coordinates_finite S H
  let K := J ⊕ (Σ i : I, OriginalNamedHiddenCoordinate S H (sort i))
  let requests : K → AnchorRequest S H := fun k => match k with
    | .inl j => q j
    | .inr ⟨i,D⟩ => ⟨sort i,D,Quotient.mk D.val.val (old i)⟩
  let oldTags : I → Sigma X := fun i => ⟨sort i,old i⟩
  obtain ⟨anchors,hAnchors,hRep⟩ := finite_actual_anchors S H sap requests
    (A ∪ Set.range oldTags) (hA.union (Set.finite_range _))
  let B := Set.range anchors
  have hB : B.Finite := Set.finite_range _
  have hAvoid (i : I) : oldTags i ∉ B := by
    rintro ⟨k,hk⟩
    exact (hRep k).2 (Or.inr ⟨i,hk.symm⟩)
  obtain ⟨fresh,hFresh,hNewOff,hFine,hOldFine⟩ :=
    split_real_family_over_frame S H sap sort old A B hA hB hAvoid
  let anchor : J → Sigma X := fun j => anchors (.inl j)
  let A' : FiniteInduced (X := X) :=
    ⟨(A ∪ B) ∪ Set.range (fun i => (⟨sort i,fresh i⟩ : Sigma X)),
      (hA.union hB).union (Set.finite_range _)⟩
  have hAnchorFine (i : I) (k : K) :
      S.colour (fresh i) (anchors k).2 = S.colour (old i) (anchors k).2 :=
    hFine i ⟨anchors k,⟨k,rfl⟩⟩
  refine ⟨fresh,anchor,A',fun _ h => Or.inl (Or.inl h),hFresh,
    hAnchors.comp Sum.inl_injective,fun j => (hRep (.inl j)).1,?_,
    fun i => Or.inr ⟨i,rfl⟩,fun j => Or.inl (Or.inr ⟨.inl j,rfl⟩),?_,hOldFine,?_⟩
  · intro i j h
    exact hNewOff i (Or.inr ⟨.inl j,h.symm⟩)
  · intro i D
    obtain ⟨a,ha,hq⟩ := (hRep (.inr ⟨i,D⟩)).1
    change Quotient.mk D.val.val a = Quotient.mk D.val.val (old i) at hq
    have hf := hAnchorFine i (.inr ⟨i,D⟩)
    rw [ha] at hf
    exact anchored_coordinate_eq S D.val (old i) (fresh i) a
      (Quotient.exact hq.symm) hf.symm
  · intro i j R
    obtain ⟨a,ha,hq⟩ := (hRep (.inl j)).1
    have hf := hAnchorFine i (.inl j)
    rw [ha] at hf
    exact anchored_mixed_binary_iff S H (old i) (fresh i) (q j).2.1 (q j).2.2 a hq hf.symm R

end
end CCO.HiddenSAPReadings
