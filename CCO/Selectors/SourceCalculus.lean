import CCO.Selectors.Basic
import CCO.SAPEdge
import CCO.SAPPoint

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The selector calculus is discharged by accepted original source theorems. -/
theorem exactCalculus_of_SAP_CCO (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) : ExactCalculus S := by
  refine ⟨?_,?_,?_,?_⟩
  · exact fun hA hB => StrongExact.exact_product_of_SAP_CCO S H sap cco hA hB
  · exact fun hA => StrongExact.exact_opposite_of_gluing S
      (S.realEdgeGluing_of_SAP H sap) hA
  · exact fun menus hE hP => StrongExact.exact_helly_of_SAP_CCO S H sap cco menus hE hP
  · intro i j k P A B hP hA hB hAB
    obtain ⟨hPn,p,hp⟩ := hP
    obtain ⟨hAn,a,ha⟩ := hA
    obtain ⟨hBn,b,hb⟩ := hB
    subst P; subst A; subst B
    have h := StrongExact.product_distrib_right_exact_of_SAP_CCO S H sap cco
      p [a,b] hPn (by simpa [StrongExact.flattenedPresentations,
        StrongExact.present_append] using hAB)
    simpa [StrongExact.flattenedPresentations, StrongExact.present_append,
      Set.setOf_and] using h

end CCO.Selectors
