import CCO.OldIdempotentForest.GapClosed

/-! B058 C15--C18. Literal OLD gap equations restrict to the retained
closed support and survive ANY homomorphism. Every required named
coordinate is obtained from the actual source certificate. FULL envelope
membership precedes the separate, distinct-representative diversity step. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.QuotientTransport
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Hidden" => originalCompletedStructure S H sap nr2
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

/-- Restrict the actual OLD equality before applying the homomorphism.
No injectivity, reflection, or embedding of the retained support is used. -/
theorem gap_coordinate_under_hom {b c : P}
    {hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c}
    {D : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c)}
    (certificate : GapCoordinateCertificate S H sap nr2 F hij D)
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : CCO.UnarySupport.Structure.Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩) :
    D.val (Eq.mp (congrArg X hij) x) y := by
  obtain ⟨a,ha,hac⟩ := gap_literal_restrict S H sap nr2 hA hb hc certificate.equation
  have hleft := (originalPartialTarget S H sap nr2).eval_functional
    (oldTerm S H sap nr2 certificate.left)
    (f.map_eval _ ha)
    (oldTerm_target_eval S H sap nr2 certificate.left (f.point ⟨b,hb⟩) (f.sort_eq ⟨b,hb⟩))
  have hright := (originalPartialTarget S H sap nr2).eval_functional
    (oldTerm S H sap nr2 certificate.right)
    (f.map_eval _ hac)
    (oldTerm_target_eval S H sap nr2 certificate.right (f.point ⟨c,hc⟩) (f.sort_eq ⟨c,hc⟩))
  have hread : (Hidden).eval certificate.left (rootMap S H sap nr2 (F.sort b) x) =
      (Hidden).eval certificate.right (rootMap S H sap nr2 (F.sort c) y) :=
    (congrArg ((Hidden).eval certificate.left) hx).trans
      (hleft.symm.trans (hright.trans (congrArg ((Hidden).eval certificate.right) hy).symm))
  exact Quotient.exact ((original_completed_hidden_node_injective S H D)
    ((certificate.left_reading x).symm.trans (hread.trans (certificate.right_reading y))))

/-- Source OGC under ANY homomorphism from the actual retained closed
boundary. The named-coordinate family is discharged by source OLD
equations, and the terminal exact-MI adapter reconstructs the FULL RAW
envelope, including its empty-family Top boundary. -/
theorem old_gap_boundary_envelope
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {b c : P} (path : SourceMacroPath S H sap nr2 F b c)
    (hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c)
    (idem : S.product (PositiveWord.profile S (gapCloseWord S hij path.flatten))
      (PositiveWord.profile S (gapCloseWord S hij path.flatten)) =
        PositiveWord.profile S (gapCloseWord S hij path.flatten))
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : CCO.UnarySupport.Structure.Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩) :
    envelope S (PositiveWord.profile S (gapCloseWord S hij path.flatten)) idem
      (Eq.mp (congrArg X hij) x) y := by
  apply (gap_envelope_iff_named_coordinates S H sap nr2 cco
    (gapCloseWord S hij path.flatten) idem (Eq.mp (congrArg X hij) x) y).mpr
  intro D above
  obtain ⟨certificate⟩ := old_gap_coordinate_equation S H sap nr2 F hUnary path hij idem D above
  exact gap_coordinate_under_hom S H sap nr2 F certificate hA hb hc f x y hx hy

/-- Casting the endpoint sort does not change any original word letter
or the resulting cross-sort diversity relation. -/
theorem gap_original_profile_of_closed {i j : ι} (hij : i = j)
    (W : PositiveWord S i j) (x : X i) (y : X j)
    (h : S.menuRel (PositiveWord.profile S (gapCloseWord S hij W))
      (Eq.mp (congrArg X hij) x) y) :
    S.menuRel (PositiveWord.profile S W) x y := by
  cases hij
  exact h

/-- Diversity follows only after actual representative distinctness.
The conclusion uses the EXACT original cross-sort flattened word. -/
theorem old_gap_boundary_diversity
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {b c : P} (path : SourceMacroPath S H sap nr2 F b c)
    (hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c)
    (idem : S.product (PositiveWord.profile S (gapCloseWord S hij path.flatten))
      (PositiveWord.profile S (gapCloseWord S hij path.flatten)) =
        PositiveWord.profile S (gapCloseWord S hij path.flatten))
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : CCO.UnarySupport.Structure.Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩)
    (hne : Eq.mp (congrArg X hij) x ≠ y) :
    S.menuRel (PositiveWord.profile S path.flatten) x y := by
  apply gap_original_profile_of_closed S hij path.flatten x y
  apply (envelope_distinct_iff S _ idem hne).mp
  exact old_gap_boundary_envelope S H sap nr2 F hUnary cco path hij idem hA hb hc f x y hx hy

theorem gap_cast_ne_of_tagged {i j : ι} (hij : i = j) (x : X i) (y : X j)
    (hne : (Sigma.mk i x : Sigma X) ≠ Sigma.mk j y) :
    Eq.mp (congrArg X hij) x ≠ y := by
  cases hij
  intro h
  exact hne (congrArg (Sigma.mk i) h)

/-- The caller may express actual diversity in the original tagged
real points. Distinct formal source vertices alone are insufficient. -/
theorem old_gap_boundary_diversity_of_tagged
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {b c : P} (path : SourceMacroPath S H sap nr2 F b c)
    (hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c)
    (idem : S.product (PositiveWord.profile S (gapCloseWord S hij path.flatten))
      (PositiveWord.profile S (gapCloseWord S hij path.flatten)) =
        PositiveWord.profile S (gapCloseWord S hij path.flatten))
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : CCO.UnarySupport.Structure.Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩)
    (hne : (Sigma.mk (gapSort S H sap nr2 F b) x : Sigma X) ≠
      Sigma.mk (gapSort S H sap nr2 F c) y) :
    S.menuRel (PositiveWord.profile S path.flatten) x y := by
  exact old_gap_boundary_diversity S H sap nr2 F hUnary cco path hij idem hA hb hc f x y hx hy
    (gap_cast_ne_of_tagged hij x y hne)

end
end CCO.OldIdempotentForest
