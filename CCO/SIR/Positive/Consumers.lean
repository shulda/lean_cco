import CCO.SIR.Positive.Source
import CCO.SIR.Positive.PrescribedMap

/-! Downstream consumers use the actual source headline with every original
provider discharged. The finite map itself and each named parameter survive. -/
universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Empty bases retain the sort-tagged STRONG Top, including equal sort
names. No equality atom or chosen return path is inserted. -/
theorem independent_empty_base (H : HomogeneousSource S G) (sap : AgeSAP S)
    (h : Selectors.HereditarySelector S) (A B : Finset (Sigma X)) :
    Independent S h A ∅ B ↔
      (∀ x ∈ A, x ∈ B → False) ∧
      ∀ x ∈ A, ∀ y ∈ B,
        S.colour x.2 y.2 = some (h.choose Set.univ (StrongExact.exact_top_of_SAP S H sap)) := by
  simp only [Independent,Finset.notMem_empty,not_false_eq_true,forall_const,SelectedPair,baseMenu_empty]
  constructor
  · rintro ⟨ho,hc⟩
    exact ⟨ho,fun x hx y hy => (hc x hx y hy).choose_spec⟩
  · rintro ⟨ho,hc⟩
    exact ⟨ho,fun x hx y hy => ⟨StrongExact.exact_top_of_SAP S H sap,hc x hx y hy⟩⟩

/-- ONE original selector supplies actual independent real copies over
EVERY prescribed finite real base and right side. -/
theorem source_real_type_existence (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : Selectors.OriginalNR2 S) :
    ∃ h : Selectors.HereditarySelector S, ∀ A B C : Finset (Sigma X),
      ∃ g : G, (∀ c ∈ C, g • c = c) ∧ Independent S h (transport g A) C B := by
  obtain ⟨h,hi⟩ := source_stationaryIndependence S H sap cco nr2
  exact ⟨h,hi.existence⟩

/-- Every PRESCRIBED base-fixing finite isomorphism extends pointwise,
with no quotient action, countability or unexpanded provider premise. -/
theorem source_prescribed_map_stationarity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : Selectors.OriginalNR2 S) :
    ∃ h : Selectors.HereditarySelector S, ∀ (A A' B C : Finset (Sigma X))
      (f : ↥(A ∪ C) ≃ ↥(A' ∪ C)),
      (∀ x y, taggedColour S x.val y.val = taggedColour S (f x).val (f y).val) →
      (∀ c (hc : c ∈ C), (f ⟨c,Finset.mem_union_right A hc⟩).val = c) →
      Independent S h A C B → Independent S h A' C B →
      ∃ g : G, (∀ b ∈ B ∪ C, g • b = b) ∧
        ∀ x : ↥(A ∪ C), g • x.val = (f x).val := by
  obtain ⟨h,hi⟩ := source_stationaryIndependence S H sap cco nr2
  refine ⟨h,?_⟩
  intro A A' B C f hcol hfix hA hA'
  exact hi.prescribed_map_stationarity H A A' B C f hcol hfix hA hA'

end CCO.SIR.Positive
