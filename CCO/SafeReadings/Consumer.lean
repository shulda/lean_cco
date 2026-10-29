import CCO.SafeReadings.SafeCompletion
import CCO.SafeReadings.AugmentedCalculus
import CCO.SafeReadings.RectangularReadings
import CCO.SafeReadings.SmallPC

/-! One joint augmented reading supplies safe completion AND original
moving readings. Formal owners and reading parameters may all repeat.
No selected realization or origin section is made equivariant. -/
universe u v w z t r s
namespace CCO.SafeReadings
open Selectors StrongExact StrongPC
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {safe : ∀ i j, S.Menu i j}

def SelectorOn.original (h : SelectorOn S (augmentedFamily S safe)) : HereditarySelector S where
  choose := fun D hD => h.choose D (Or.inl hD)
  member := fun D hD => h.member D (Or.inl hD)
  opposite := fun D hD hOpp => h.opposite D (Or.inl hD) (Or.inl hOpp)
  heredity := fun E D hE hD hED hSurvive => h.heredity E D (Or.inl hE) (Or.inl hD) hED hSurvive
  pc := fun D E P hD hE hP hpc => h.pc D E P (Or.inl hD) (Or.inl hE) (Or.inl hP) hpc

theorem SelectorOn.original_covariant {Γ : Type z} [Group Γ] {N : Type t}
    (h : SelectorOn S (augmentedFamily S safe)) (A : PureTagAction S Γ N)
    (hInv : A.Invariant (augmentedFamily S safe)) (hCov : h.Covariant A hInv) :
    (h.original S).Covariant S A := by
  intro g D hD
  exact hCov g D (Or.inl hD)

theorem completion_and_independent_readings
    {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S)
    (hs : SafeSystem S safe) (age : TriangleAge.{u,v,w,s} S)
    {Γ : Type z} [Group Γ] {N : Type t} (A : PureTagAction S Γ N)
    (hInv : A.Invariant (augmentedFamily S safe))
    (h : SelectorOn S (augmentedFamily S safe)) (hCov : h.Covariant A hInv)
    (hSafe : ∀ {i j} (D : S.Menu i j) (hD), (D ∩ safe i j).Nonempty → h.choose D hD ∈ safe i j)
    {V : Type s} (D : PartialDiagram S V) (hComp : D.HasStrongCompletion)
    {K : Type r} [CommGroup K] (E : EndpointGauge S A K) (hConv : LiteralConverse S A)
    (g k l : K) {i j m} (L : S.Menu i j) (M : S.Menu j m) (P : S.Menu i m)
    (hL : Exact S L) (hM : Exact S M) (hP : Exact S P) (hPC : S.PC L M P) :
    let C := canonicalDiagram S H sap cco D hComp h
    C.diagram.HasStrongCompletion ∧
      (∀ x y hxy a, D.edge x y hxy = some a → C.diagram.edge x y hxy = some a) ∧
      (∀ x y hxy, D.edge x y hxy = none →
        ∃ a ∈ safe (D.vertexSort x) (D.vertexSort y), C.diagram.edge x y hxy = some a) ∧
      (Nat.card V ≤ 2 → fixedNetwork D = initial D) ∧
      S.Triangle (reading E (h.original S) g L hL)
        (reading E (h.original S) k M hM) (reading E (h.original S) l P hP) := by
  refine ⟨canonicalDiagram_in_age S H sap cco D hComp h age,?_,?_,?_,?_⟩
  · intro x y hxy a ha
    exact canonicalDiagram_records S H sap cco D hComp h hxy a ha
  · intro x y hxy hhole
    exact ⟨canonicalAtom S H sap cco D hComp h ⟨x,y,hxy⟩,
      canonicalDiagram_safe S H sap cco D hComp h hs hSafe hxy hhole,rfl⟩
  · exact small_fixedNetwork_eq_initial D
  · exact rectangular_reading_triangle E (h.original S)
      (h.original_covariant S A hInv hCov) hConv (exactCalculus_of_SAP_CCO S H sap cco)
      (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap) g k l L M P hL hM hP hPC

end CCO.SafeReadings
