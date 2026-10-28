import CCO.SIR.Positive.Existence
import CCO.SIR.Positive.Transitivity
import CCO.SIR.Positive.NaturalSpan
import Mathlib.Basic.Finite.Prod

/-! Conditional and source-discharge levels of the positive SIR theorem.
No countability, EPPA or Ramsey premise occurs. -/
universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- C13: one supplied exact calculus, ONE joint hereditary selector and
actual triangle fullness produce the displayed finite-real-set SIR. -/
theorem selected_stationaryIndependence (H : HomogeneousSource S G) (sap : AgeSAP S)
    (K : Selectors.ExactCalculus S) (h : Selectors.HereditarySelector S)
    (fullness : TriangleFullness S) :
    StationaryIndependence (G := G) (Independent S h) := by
  have hPoint : S.RealPointGluing := S.realPointGluing_of_SAP H sap
  have hEdge : S.RealEdgeGluing := S.realEdgeGluing_of_SAP H sap
  exact {
    normalization := independent_normalization S h
    invariance := independent_transport S H h
    symmetry := independent_symmetry S K h
    restriction := fun A B C A' B' hA hB => independent_restriction S h hA hB
    transitivity := independent_transitivity S K hPoint hEdge h
    existence := independent_exists S H sap K h fullness hPoint hEdge
    stationarity := independent_stationarity S H h
  }

/-- C14: all conditional parameters are discharged from the actual
named-sort homogeneous SAP+CCO source and FULL original sortwise NR2. -/
theorem source_stationaryIndependence (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : Selectors.OriginalNR2 S) :
    ∃ h : Selectors.HereditarySelector S,
      StationaryIndependence (G := G) (Independent S h) := by
  obtain ⟨h⟩ := Selectors.exists_hereditary_selector_of_SAP_CCO_NR2 S H sap cco nr2
  exact ⟨h,selected_stationaryIndependence S H sap
    (Selectors.exactCalculus_of_SAP_CCO S H sap cco) h
    (triangleFullness_of_homogeneous_CCO S H cco)⟩

/-- The stronger no-finite-relative-index assumption is stated on ALL
original invariant equivalences and actual relative quotient classes. -/
def NoFiniteRelativeIndex : Prop :=
  ∀ (i : ι) (R T : Setoid (X i)),
    Selectors.ColourInvariantSetoid S R → Selectors.ColourInvariantSetoid S T →
    (∀ x y, R x y → T x y) → R ≠ T → ∀ a : X i,
      Infinite (Quotient (R.comap (fun x : {x // T a x} => x.val)))

/-- A literal two-class decomposition makes the actual relative
quotient finite; no Hasse theorem or exactness assumption is used. -/
theorem noFiniteRelativeIndex_implies_NR2 (hNo : NoFiniteRelativeIndex S) :
    Selectors.OriginalNR2 S := by
  intro i R T hR hT htwo
  let a := Classical.choice (S.nonemptySort i)
  obtain ⟨b,hab,hnab,hclasses⟩ := htwo.2 a
  have hne : R ≠ T := by intro he; exact hnab (he ▸ hab)
  let Q := Quotient (R.comap (fun x : {x // T a x} => x.val))
  let f : Bool → Q := fun bit => if bit then Quotient.mk _ ⟨b,hab⟩ else Quotient.mk _ ⟨a,T.refl a⟩
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ z =>
      rcases (hclasses z.val).mp z.property with hz | hz
      · refine ⟨false,?_⟩
        exact Quotient.sound hz
      · refine ⟨true,?_⟩
        exact Quotient.sound hz
  letI : Finite Q := Finite.of_surjective f hsurj
  letI : Infinite Q := hNo i R T hR hT htwo.1 hne a
  exact not_finite Q

/-- The one-sort stronger premise, and indeed its named-sort extension,
is only used to derive NR2 before applying the already discharged headline. -/
theorem source_stationaryIndependence_of_noFiniteRelative
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (hNo : NoFiniteRelativeIndex S) :
    ∃ h : Selectors.HereditarySelector S,
      StationaryIndependence (G := G) (Independent S h) :=
  source_stationaryIndependence S H sap cco (noFiniteRelativeIndex_implies_NR2 S hNo)

end CCO.SIR.Positive
