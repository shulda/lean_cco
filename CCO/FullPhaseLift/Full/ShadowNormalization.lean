import CCO.FullPhaseLift.Full.ActualShadow
import CCO.FullPhaseLift.BinarySource.ActualExtension

/-! Source-shadow normalization is proved from actual pair CCO+SAP, using
only local signed interpretation. Pair homogeneity is DERIVED from full
homogeneity and raw A03 in the final canonical-prefix corollary. -/

universe v w
namespace CCO.FullPhaseLift.Full.Shadow
open Canonical
noncomputable section
variable {L : Signature} {M : Type w} {V : Type v}
variable (U : BoolTable L M) (hsym : SameSortSymmetric U)

/-- Accepted CCO+SAP injectivization is applied to the specified atomic
shadow. Its output still interprets each signed low declaration locally. -/
theorem CertifiedPairCompletion.strict_target
    {G : Type*} [Group G] [∀ i, MulAction G (Carrier U i)]
    (H : HomogeneousSource (source U hsym) G)
    (sap : AgeSAP (source U hsym)) (cco : SemanticCCO.{0,w,v,0} (source U hsym))
    {D : Partial L V} {m : ℕ} {F : Fin m → FrozenFactor U D}
    (C : CertifiedPairCompletion U hsym D F) : PairCompletion U D F := by
  obtain ⟨f,hf⟩ :=
    (CCO.PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
      H sap cco C.diagram).mpr C.cycles
  let p : V ↪ M := ⟨(pack U).symm ∘ f.image,(pack U).symm.injective.comp hf⟩
  exact PairCompletion.of_actual F p (C.low.interpret U hsym f)

theorem of_strict
    {G : Type*} [Group G] [∀ i, MulAction G (Carrier U i)]
    (H : HomogeneousSource (source U hsym) G)
    (sap : AgeSAP (source U hsym)) (cco : SemanticCCO.{0,w,0,0} (source U hsym))
    (normal : Full.StrictSupportNormal U) : SupportNormal U hsym := by
  intro n D m F hc hcov hshadow
  obtain ⟨C⟩ := hshadow
  exact normal n D m F hc hcov (C.strict_target U hsym H sap cco)

/-- Exact interface equivalence on an actual homogeneous SAP+CCO canonical
pair prefix. In particular the semantic helper gate introduces no new
mathematical premise in the source theorem. -/
theorem supportNormal_iff_strict
    {G : Type*} [Group G] [∀ i, MulAction G (Carrier U i)]
    (H : HomogeneousSource (source U hsym) G)
    (sap : AgeSAP (source U hsym)) (cco : SemanticCCO.{0,w,0,0} (source U hsym)) :
    SupportNormal U hsym ↔ Full.StrictSupportNormal U :=
  ⟨fun h => h.to_strict U hsym,fun h => of_strict U hsym H sap cco h⟩

/-- No binary homogeneity callback: derive it from original FULL
homogeneity plus the source-facing raw interface, before injectivization. -/
theorem actual_binary_homogeneous [Countable M]
    (hom : (toRelational U).Homogeneous) (normal : SupportNormal U hsym) :
    HomogeneousSource (source U hsym) (TerminalPowers.FullAut (source U hsym)) :=
  BinarySource.actual_binary_homogeneous U hsym hom (normal.to_strict U hsym)

/-- At later full prefixes, preserving the internal strict helper and
FULL homogeneity suffices to re-establish the exact raw source interface;
pair homogeneity is constructed, rather than added as a callback. -/
theorem of_strict_full_homogeneous [Countable M]
    (hom : (toRelational U).Homogeneous) (normal : Full.StrictSupportNormal U)
    (sap : AgeSAP (source U hsym)) (cco : SemanticCCO.{0,w,0,0} (source U hsym)) :
    SupportNormal U hsym :=
  of_strict U hsym (BinarySource.actual_binary_homogeneous U hsym hom normal) sap cco normal

end
end CCO.FullPhaseLift.Full.Shadow
