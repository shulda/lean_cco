import CCO.TypedOrbitFrames.FullCoverSourceExports
import CCO.TypedOrbitFrames.OriginalFullGroupInclusion
import CCO.UnaryFreshFrames.Frames

/-!
# The actual source instances for hereditary hidden orbits

The carrier, functions and binary relations are the accepted interpreted
signature. The only source index hypothesis is literal FULL-cover infinitude;
the numerical NR2 provider is derived. Original motions are a subgroup of
full hidden Aut, and no converse or hidden homogeneity is used.
-/

universe u v w r
namespace CCO.HereditaryHiddenOrbits
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

abbrev terminalNR2 := original_nr2_of_all_full_covers_infinite S hCover
abbrev Carrier := OriginalCompletedNamedCarrier S H
abbrev hidden := originalCompletedStructure S H sap (terminalNR2 S hCover)
abbrev motions : Subgroup (hidden S H sap hCover).Aut :=
  originalCompletedMotionSubgroup S H sap (terminalNR2 S hCover)

/-- Literal old real vertices, not newly selected representatives in a
finite hidden base. -/
def reals : Set (Carrier S H) := Set.range Sum.inl

/-- Original pointwise orbit over an arbitrary actual hidden parameter
set. The acting group here is G, before taking its image in hidden Aut. -/
def OriginalOrbit (A : Set (Carrier S H)) (x : Carrier S H) : Set (Carrier S H) :=
  {y | ∃ g : G, (∀ a ∈ A, originalCompletedNamedAct S H g a = a) ∧
    originalCompletedNamedAct S H g x = y}

theorem motion_orbit_eq_original (A : Set (Carrier S H)) (x : Carrier S H) :
    orbitOver (motions S H sap hCover) A x = OriginalOrbit S H A x := by
  ext y
  rw [mem_orbitOver_iff]
  constructor
  · rintro ⟨g,hFix,hMove⟩
    obtain ⟨g0,hg0⟩ := g.property
    have heval (z : Carrier S H) :
        g • z = originalCompletedNamedAct S H g0 z := by
      change g.val • z = _
      rw [← hg0]
      rfl
    exact ⟨g0,fun a ha => (heval a).symm.trans (hFix a ha),
      (heval x).symm.trans hMove⟩
  · rintro ⟨g,hFix,hMove⟩
    exact ⟨⟨originalCompletedMotionHom S H sap (terminalNR2 S hCover) g,
      ⟨g,rfl⟩⟩,hFix,hMove⟩

theorem real_sort_iff (x : Carrier S H) :
    (hidden S H sap hCover).sort x ∈
      originalCompletedRealSorts S H sap (terminalNR2 S hCover) ↔
        x ∈ reals S H := by
  constructor
  · intro hx
    cases x with
    | inl p => exact ⟨p,rfl⟩
    | inr q =>
      rcases q with ⟨⟨i,J,q⟩,hNamed⟩
      obtain ⟨j,hj⟩ := hx
      change (⟨i,Sum.inr _⟩ : OriginalCompletedCoordinateCode S H) =
        ⟨j,Sum.inl ()⟩ at hj
      cases hj
  · rintro ⟨⟨i,x⟩,rfl⟩
    exact ⟨i,rfl⟩

/-- Every actual hidden vertex has an actual original real generator,
even if the finite closed set containing it has no real vertices. -/
theorem real_generating : (hidden S H sap hCover).RealGenerating (reals S H) := by
  intro x
  obtain ⟨p,hp⟩ := original_completed_structure_point_generated S H sap
    (terminalNR2 S hCover) x
  exact ⟨.inl p,⟨p,rfl⟩,hp⟩

/-- The singleton provider concerns actual term values, including orphan
inputs, rather than a finite bound on syntactic words. -/
theorem locally_finite : (hidden S H sap hCover).LocallyFinite :=
  (hidden S H sap hCover).locallyFinite_of_singletons
    (original_completed_all_singleton_closures_finite S H sap (terminalNR2 S hCover))

theorem singleton_bound (x : Carrier S H) :
    ((hidden S H sap hCover).closureAt x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  rw [original_completed_structure_closureAt_eq]
  exact original_completed_any_generator_uniform S H sap (terminalNR2 S hCover) x

theorem real_invariant :
    (hidden S H sap hCover).InvariantReal (motions S H sap hCover) (reals S H) := by
  intro g x hx
  obtain ⟨p,rfl⟩ := hx
  obtain ⟨g0,hg0⟩ := g.property
  refine ⟨g0 • p,?_⟩
  change (Sum.inl (g0 • p) : Carrier S H) = g.val • (Sum.inl p : Carrier S H)
  rw [← hg0]
  rfl

/-- The actual fresh representative construction supplies the exact
frame/base intersection for EVERY finite closed base, without a real-root,
compatibility, hidden SAP or hidden homogeneity premise. -/
theorem fresh_frames : (hidden S H sap hCover).FreshFrames (reals S H) := by
  intro A B hA hB hClosedA _ hAB
  obtain ⟨D,hD,hReal,hGen,hFresh⟩ :=
    CCO.TypedOrbitFrames.Source.fresh_real_frame S hCover H sap
      A B ∅ hA hClosedA hB Set.finite_empty hAB
  refine ⟨D,hD,?_,hGen,?_⟩
  · intro x hx
    exact (real_sort_iff S H sap hCover x).mp (hReal hx)
  · simpa only [Set.union_empty] using hFresh

/-- A finite set of genuine real vertices is the image of exactly its
old real points; nothing is inserted into an orphan hidden base. -/
theorem real_preimage_image {D : Set (Carrier S H)} (hD : D ⊆ reals S H) :
    Sum.inl '' (Sum.inl ⁻¹' D : Set (Sigma X)) = D := by
  apply Set.image_preimage_eq_of_subset
  exact hD

/-- Discharge B039 real-base infinitude using the complete old induced
real diagram and the accepted original-group source theorem. -/
theorem real_base_orbits (cco : SemanticCCO.{u,v,max u v,w} S) :
    (hidden S H sap hCover).RealBaseOrbits (motions S H sap hCover) (reals S H) := by
  intro D hD hReal x hx
  let oldD : Set (Sigma X) := Sum.inl ⁻¹' D
  have hOldD : oldD.Finite := hD.preimage Sum.inl_injective.injOn
  have hImage : Sum.inl '' oldD = D := real_preimage_image S H hReal
  have hxOld : x ∉ originalCompletedRealBaseClosure S H sap (terminalNR2 S hCover) oldD := by
    rw [← original_completed_structure_real_base_closure_eq,hImage]
    exact hx
  have hInf := CCO.TypedOrbitFrames.Source.outside_real_base_orbit_infinite
    S hCover H sap cco oldD hOldD x hxOld
  apply hInf.mono
  rintro y ⟨g,hg,hMove⟩
  rw [motion_orbit_eq_original]
  refine ⟨g,?_,hMove⟩
  intro a ha
  rw [← hImage] at ha
  obtain ⟨p,hp,rfl⟩ := ha
  exact congrArg Sum.inl (hg p hp)

end
end CCO.HereditaryHiddenOrbits
