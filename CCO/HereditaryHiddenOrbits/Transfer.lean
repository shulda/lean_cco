import CCO.HereditaryHiddenOrbits.ActualSource

/-!
# Original-group orbits over arbitrary actual closed hidden bases

The exact source instances discharge the accepted generic B039 frame
theorem. The explicit frame witness below additionally exposes the same
finite real D, the same off-base vertex, and the pointwise stabilizer
containment used in the proof. No hidden partial-map extension is involved.
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

/-- The actual test extension is finite and closed. Its fresh real
frame generates A while excluding the SPECIFIED same actual x. -/
theorem off_base_real_frame
    (A : Set (Carrier S H)) (hA : A.Finite)
    (hClosed : (hidden S H sap hCover).Closed A)
    (x : Carrier S H) (hx : x ∉ A) :
    ∃ D : Set (Carrier S H), D.Finite ∧ D ⊆ reals S H ∧
      A ⊆ (hidden S H sap hCover).closure D ∧
      x ∉ (hidden S H sap hCover).closure D ∧
      fixer (motions S H sap hCover) D ≤ fixer (motions S H sap hCover) A := by
  let C := hidden S H sap hCover
  let B := C.closure (A ∪ {x})
  have hAB : A ⊆ B := fun a ha => C.subset_closure _ (Or.inl ha)
  have hxB : x ∈ B := C.subset_closure _ (Or.inr rfl)
  obtain ⟨D,hD,hReal,hDA,hDB⟩ := fresh_frames S H sap hCover A B hA
    (locally_finite S H sap hCover _ (hA.union (Set.finite_singleton x)))
    hClosed (C.closure_closed _) hAB
  refine ⟨D,hD,hReal,hDA,?_,?_⟩
  · intro hxD
    exact hx (hDB ▸ (show x ∈ C.closure D ∩ B from ⟨hxD,hxB⟩))
  · intro g hg a ha
    exact C.closure_fixed g.val hg a (hDA ha)

/-- C12: apply the accepted forward frame theorem with ALL original
source instances proved in ActualSource, rather than requested anew. -/
theorem infinite_closed_motion_orbits
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (hidden S H sap hCover).InfiniteClosedOrbits (motions S H sap hCover) :=
  (hidden S H sap hCover).infiniteClosedOrbits_of_frames
    (motions S H sap hCover) (locally_finite S H sap hCover)
    (fresh_frames S H sap hCover) (real_base_orbits S H sap hCover cco)

/-- HO holds for EVERY finite actual unary-closed hidden base, including
empty and orphan-only bases, in the original induced group. -/
theorem original_hidden_closed_orbit_infinite
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (A : Set (Carrier S H)) (hA : A.Finite)
    (hClosed : (hidden S H sap hCover).Closed A)
    (x : Carrier S H) (hx : x ∉ A) :
    (OriginalOrbit S H A x).Infinite := by
  rw [← motion_orbit_eq_original S H sap hCover]
  exact infinite_closed_motion_orbits S H sap hCover cco A hA hClosed x hx

/-- Fixing the parameter set fixes every unary term value pointwise;
therefore the exact ORIGINAL stabilizers, not only their orbits, agree. -/
theorem original_fixer_closure_eq (T : Set (Carrier S H)) :
    fixer (motions S H sap hCover) ((hidden S H sap hCover).closure T) =
      fixer (motions S H sap hCover) T :=
  (hidden S H sap hCover).fixer_closure_eq _ _

theorem original_acl_eq_closure
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite) :
    Acl (motions S H sap hCover) T = (hidden S H sap hCover).closure T :=
  (hidden S H sap hCover).acl_eq_closure _ (locally_finite S H sap hCover)
    (infinite_closed_motion_orbits S H sap hCover cco) hT

theorem original_dcl_eq_closure
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite) :
    Dcl (motions S H sap hCover) T = (hidden S H sap hCover).closure T :=
  (hidden S H sap hCover).dcl_eq_closure _ (locally_finite S H sap hCover)
    (infinite_closed_motion_orbits S H sap hCover cco) hT

/-- C13--C16 directly in the pre-image original group: orbit membership
and not just the range-subgroup packaging identify finite orbits with terms. -/
theorem original_finite_orbit_iff_closure
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (T : Set (Carrier S H)) (hT : T.Finite) (x : Carrier S H) :
    (OriginalOrbit S H T x).Finite ↔ x ∈ (hidden S H sap hCover).closure T := by
  rw [← motion_orbit_eq_original S H sap hCover]
  change x ∈ Acl (motions S H sap hCover) T ↔ _
  rw [original_acl_eq_closure S H sap hCover cco T hT]

end
end CCO.HereditaryHiddenOrbits
