import CCO.OldIdempotentForest.GapPath

/-! Reversing a traversed ORIGINAL macro side retains its SAME old
complete factor. The reversed pair menu is proved to imply the opposite
original menu by one actual original pair motion; it is never replaced
by an independently chosen model of the reversed old endpoints. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

/-- ALL comparisons of the original old pair are transported together
by the actual root-pair motion furnished by a reversed fine survivor. -/
theorem gap_pairMenu_reverse {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom D.down.1 C.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 s q)) :
    S.conv a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  obtain ⟨g,hS,hQ⟩ := root_pair_motion_of_surviving_atom S H sap nr2 s q ha hxy
  let qy : (Hidden).Carrier C :=
    ⟨(Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,y⟩),
      (Hidden).eval_sort (rootBaseTerm S H sap nr2 C) rfl⟩
  let sx : (Hidden).Carrier D :=
    ⟨(Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,x⟩),
      (Hidden).eval_sort (rootBaseTerm S H sap nr2 D) rfl⟩
  have hyx : S.atomRel (S.conv a) y x := (S.colour_swap x y a).mp hxy
  rintro _ ⟨d,hd,rfl⟩
  have hMoved : d.Holds qy sx := d.motion_preserves
    (q := q) (s := s) (q' := qy) (s' := sx) g hQ hS hd
  have hPullback : d.pullback.Holds y x :=
    (d.pullback_holds_iff qy sx y x rfl rfl).mpr hMoved
  exact d.pullback.atom_mem_of_holds hyx hPullback

variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

namespace SupportedMacroSide
variable {S H sap nr2 F} {b c : P}

/-- Reverse the EXACT original atomic word and swap the two generators
of its SAME induced complete support. Its menu condition is proved from
actual simultaneous old pair comparisons, not postulated for a new model. -/
def reverse (side : SupportedMacroSide S H sap nr2 F b c) :
    SupportedMacroSide S H sap nr2 F c b where
  word := StrongExact.reverseWord S side.word
  distinct := side.distinct.symm
  joined := by rw [Set.pair_comm c b]; exact side.joined
  model := pairSwapEmbedding S H sap nr2 F (b := c) (c := b) side.model
  contains := by
    intro a ha
    have hReverse : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 side.right side.left) := ha
    have hOriginal : S.conv a ∈ side.menu :=
      gap_pairMenu_reverse S H sap nr2 side.left side.right hReverse
    have hOpposite : a ∈ S.opposite (PositiveWord.profile S side.word) :=
      side.contains hOriginal
    have hProfile := profile_reverse_of_gluing S (S.realEdgeGluing_of_SAP H sap) side.word
    exact hProfile.symm ▸ hOpposite

@[simp] theorem reverse_word (side : SupportedMacroSide S H sap nr2 F b c) :
    side.reverse.word = StrongExact.reverseWord S side.word := rfl

end SupportedMacroSide
end
end CCO.OldIdempotentForest
