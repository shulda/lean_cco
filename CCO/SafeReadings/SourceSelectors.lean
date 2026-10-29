import CCO.SafeReadings.ReturnIterations
import CCO.SafeReadings.OriginalSelector

/-! Source discharges for positive no-return and the original joint
covariant selector. No NoReturn or selector provider remains an input.
The augmented Q engine is separate from this ORIGINAL-H consumer. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Parallel generated-family separation for ANY family of nonempty raw
menus. It needs neither original exactness, CCO, nor a safe palette. -/
theorem source_noReturn
    {G : Type*} [Group G] [∀ i, MulAction G (X i)] [Finite Λ]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (primitive : SortwisePrimitive S)
    (A : PureTagAction S Λ N) (hc : LiteralConverse S A)
    {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty) :
    NoReturn S Q A := by
  let point : S.RealPointGluing := S.realPointGluing_of_SAP H sap
  let edge : S.RealEdgeGluing := S.realEdgeGluing_of_SAP H sap
  exact noReturn_of_positiveClosed_full S A point hne hc
    (positiveGenerated_closed_full S A point edge H primitive hne)

/-- The accepted ORIGINAL-H engine now has its actual positive no-return
premise proved from homogeneous primitive SAP. One selector simultaneously
preserves converse, all three PC coordinates and literal pure covariance. -/
theorem exists_original_covariant_selector
    {G : Type*} [Group G] [∀ i, MulAction G (X i)] [Fintype Λ]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (primitive : SortwisePrimitive S)
    (A : PureTagAction S Λ N) (hc : LiteralConverse S A) :
    ∃ selector : HereditarySelector S, selector.Covariant S A :=
  original_selector_of_noReturn S A H sap cco
    (source_noReturn S H sap primitive A hc (fun h => h.1))

end CCO.SafeReadings
