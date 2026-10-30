import CCO.RankInduction.FiniteRestoration
import CCO.RealClosure.Bounds.ExactDirections

/-! The finite-exact alternative uses the accepted greatest finite exact
kernel, not the possibly nonexact greatest finite original packet. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact ExactCRT ParityHasse.Original RealHull.Geometry
open RealClosure.Bounds FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

def greatestFiniteExact : ExactEq S H cco () :=
  finiteExactPacket S H (semanticCCO_change_universe S cco)

omit [Countable M] in
theorem greatestFiniteExact_classes :
    (rankKernel S H cco (greatestFiniteExact S H cco)).FiniteClasses := by
  intro x
  exact Set.finite_coe_iff.mp
    (finiteExactPacket_finite S H (semanticCCO_change_universe S cco) x)

omit [Countable M] in
theorem greatestFiniteExact_normalized
    (h : greatestFiniteExact S H cco = ⊥) : NoFiniteExactKernel S := by
  intro K finiteK B represents
  let E : ExactEq S H cco () := ⟨K.val,⟨B,represents⟩⟩
  have hclasses : FiniteClasses S K :=
    (FinitePackets.Geometry.finiteIndex_bottom_iff_finite_classes S K).mp finiteK
  have hle : E ≤ greatestFiniteExact S H cco :=
    le_finiteExactPacket S H (semanticCCO_change_universe S cco) E hclasses
  rw [h] at hle
  have he : E = ⊥ := le_bot_iff.mp hle
  apply ColourEq.ext
  intro x y
  exact Iff.of_eq (congrArg (fun F : ExactEq S H cco () => F.val.r x y) he)

omit [Countable M] in
theorem normalized_or_greatest_finite :
    NoFiniteExactKernel S ∨
      (greatestFiniteExact S H cco ≠ ⊥ ∧
        (rankKernel S H cco (greatestFiniteExact S H cco)).FiniteClasses) := by
  by_cases h : greatestFiniteExact S H cco = ⊥
  · exact Or.inl (greatestFiniteExact_normalized S H cco h)
  · exact Or.inr ⟨h,greatestFiniteExact_classes S H cco⟩

end
end CCO.RankInduction
