import CCO.FullPhaseLift.BinarySource.MarkedComparisonPatterns
import CCO.FullPhaseLift.BinarySource.ActualExtension
import CCO.FullPhaseLift.Canonical.Homogeneity
import CCO.FullPhaseLift.Marked.Inheritance

/-! The actual full marked prefix and the chosen B047 pair successor are
the SAME marked pair age, with a constructed countable pair isomorphism.
New binary homogeneity is DERIVED from the preserved full interface and
native full homogeneity. Higher relations are never transported by this
pair isomorphism. -/

universe m t
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter OwnerTransversal.CountableColour RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {L : Signature} {M : Type m} [Countable M] (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {a : UnaryName U}
variable {K : Kernel (Canonical.source U hsym) a}
variable (P : SourcePhase (Canonical.source U hsym) H C K)
variable (cco : SemanticCCO.{0,m,m,0} (Canonical.source U hsym))
variable (I : Identification (Canonical.source U hsym) H (P.completion_property cco))
variable (sap : Marked.StrongAmalgamation U (Canonical.source U hsym) (Canonical.pack U) P.masks)
variable (oldIso : Canonical.Iso
  (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) U)

def modelSym : SameSortSymmetric
    (FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) :=
  sameSortSymmetric_decoded _ oldIso hsym

include oldIso in
theorem model_motions (normal : Full.StrictSupportNormal U) :
    TupleMotions (modelTable U hsym P sap) := by
  let E := FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap
  let T := FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap
  let bits := FullReduct.bits U (Canonical.source U hsym) (Canonical.pack U) P.masks sap
  have heq : Marked.table T bits = E := Marked.table_oldTable_bits E
  have homE : (toRelational E).Homogeneous :=
    homogeneous_of_firstOrder (inferInstance : (Marked.addBit L).firstOrder.Structure (Model U hsym P sap))
      (Marked.limit_homogeneous U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)
  have normalE : Full.StrictSupportNormal E :=
    Marked.strictSupportNormal U hsym P.masks sap normal oldIso
  have homT : (toRelational (Marked.table T bits)).Homogeneous := by rw [heq]; exact homE
  have normalT : Full.StrictSupportNormal (Marked.table T bits) := by rw [heq]; exact normalE
  let hs := sameSortSymmetric_marked (sameSortSymmetric_of_iso oldIso hsym) bits
  exact codeTable_motions T bits hs (actual_binary_homogeneous (Marked.table T bits) hs homT normalT)

include oldIso in
theorem comparison_equiv (normal : Full.StrictSupportNormal U) :
    ∃ f : Model U hsym P sap ≃ NewPoint I,
      (∀ x, (targetTable U hsym P cco I).owner (f x) = (modelTable U hsym P sap).owner x) ∧
      ∀ x y, (targetTable U hsym P cco I).colour (f x) (f y) =
        (modelTable U hsym P sap).colour x y := by
  letI : Countable (NewPoint I) := (targetOld U hsym P cco I).injective.countable
  exact actual_equiv_of_same_age (modelTable U hsym P sap) (targetTable U hsym P cco I)
    (model_to_target_age U hsym P cco I sap) (target_to_model_age U hsym P cco I sap)
    (model_motions U hsym P sap oldIso normal) (target_motions U hsym P cco I)

/-- The concrete whole-carrier pattern isomorphism used to construct the
actual typed sort/fibre/atom isomorphism to the B047 successor. -/
theorem comparison_pattern (normal : Full.StrictSupportNormal U) :
    ∃ e : Sigma (Canonical.Carrier
        (FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)) ≃ NewPoint I,
      ∀ p q r s,
        taggedColour (Canonical.source
          (FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)
          (modelSym U hsym P sap oldIso)) p q =
        taggedColour (Canonical.source
          (FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)
          (modelSym U hsym P sap oldIso)) r s ↔
        taggedColour (APCharacter.SourceAge.UnarySource.source I) (e p) (e q) =
          taggedColour (APCharacter.SourceAge.UnarySource.source I) (e r) (e s) := by
  obtain ⟨f,ho,hc⟩ := comparison_equiv U hsym P cco I sap oldIso normal
  let E := FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap
  let e := (Canonical.pack E).symm.trans f
  refine ⟨e,?_⟩
  intro p q r s
  obtain ⟨x,rfl⟩ := (Canonical.pack E).surjective p
  obtain ⟨y,rfl⟩ := (Canonical.pack E).surjective q
  obtain ⟨z,rfl⟩ := (Canonical.pack E).surjective r
  obtain ⟨w,rfl⟩ := (Canonical.pack E).surjective s
  change taggedColour (Canonical.source E (modelSym U hsym P sap oldIso)) (Canonical.pack E x) (Canonical.pack E y) =
      taggedColour (Canonical.source E (modelSym U hsym P sap oldIso)) (Canonical.pack E z) (Canonical.pack E w) ↔
    taggedColour (APCharacter.SourceAge.UnarySource.source I) (f x) (f y) =
      taggedColour (APCharacter.SourceAge.UnarySource.source I) (f z) (f w)
  rw [canonical_pattern_iff,target_pattern_iff]
  change _ ↔
    (targetTable U hsym P cco I).owner (f x) = (targetTable U hsym P cco I).owner (f z) ∧
    (targetTable U hsym P cco I).owner (f y) = (targetTable U hsym P cco I).owner (f w) ∧
    (targetTable U hsym P cco I).colour (f x) (f y) = (targetTable U hsym P cco I).colour (f z) (f w)
  rw [ho,ho,ho,ho,hc,hc]
  rfl

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
