import CCO.FullPhaseLift.Full.SourceIso
import CCO.FullPhaseLift.Canonical.UnaryExpansion

/-! A genuine full-language isomorphism induces an actual isomorphism of
its canonical typed pair sources. All old higher tuples are preserved by
the FULL isomorphism first; the pair comparison never replaces it. -/

set_option backward.isDefEq.respectTransparency.types false
universe v w
namespace CCO.FullPhaseLift.Full
open Canonical
noncomputable section
variable {L : Signature} {M : Type v} {N : Type w}
variable {A : BoolTable L M} {B : BoolTable L N}

/-- Exact untyped optional canonical names, including the real diagonal,
are preserved under an actual full isomorphism. -/
theorem pairNameCode_iso (f : Canonical.Iso A B) (x y : M) :
    pairNameCode B (f.point x) (f.point y) = pairNameCode A x y := by
  have hu (z : M) : unaryProfile B (f.point z) = unaryProfile A z :=
    unaryProfile_embedding f.toEmbedding z
  have hp : pairProfile B (f.point x) (f.point y) = pairProfile A x y :=
    pairProfile_embedding f.toEmbedding x y
  unfold pairNameCode
  rw [hu x,hu y,hp]
  by_cases hxy : x = y
  · rw [if_pos (congrArg f.point hxy),if_pos hxy]
  · rw [if_neg (fun h => hxy (f.point.injective h)),if_neg hxy]

def canonicalWhole (f : Canonical.Iso A B) : Sigma (Carrier A) ≃ Sigma (Carrier B) :=
  (pack A).symm.trans (f.point.trans (pack B))

theorem canonicalWhole_pattern (f : Canonical.Iso A B)
    (ha : SameSortSymmetric A) (hb : SameSortSymmetric B)
    (p q r s : Sigma (Carrier A)) :
    taggedColour (source A ha) p q = taggedColour (source A ha) r s ↔
      taggedColour (source B hb) (canonicalWhole f p) (canonicalWhole f q) =
        taggedColour (source B hb) (canonicalWhole f r) (canonicalWhole f s) := by
  have flatten (x : Sigma (Carrier A)) : pack A ((pack A).symm x) = x :=
    (pack A).apply_symm_apply x
  have hA (x y : Sigma (Carrier A)) :
      tagCode A (taggedColour (source A ha) x y) =
        pairNameCode A ((pack A).symm x) ((pack A).symm y) := by
    rw [← flatten x,← flatten y]
    exact tagCode_pack_eq_pairNameCode A ha _ _
  have hB (x y : Sigma (Carrier A)) :
      tagCode B (taggedColour (source B hb) (canonicalWhole f x) (canonicalWhole f y)) =
        pairNameCode A ((pack A).symm x) ((pack A).symm y) := by
    change tagCode B (taggedColour (source B hb)
      (pack B (f.point ((pack A).symm x))) (pack B (f.point ((pack A).symm y)))) = _
    rw [tagCode_pack_eq_pairNameCode,pairNameCode_iso]
  constructor
  · intro h
    apply tagCode_injective B
    rw [hB,hB,← hA p q,← hA r s,h]
  · intro h
    apply tagCode_injective A
    rw [hA,hA,← hB p q,← hB r s,h]

/-- The source comparison is derived from full isomorphism and complete
canonical types. No separate palette/sort correspondence is supplied. -/
def canonicalSourceIso (f : Canonical.Iso A B)
    (ha : SameSortSymmetric A) (hb : SameSortSymmetric B) :
    SourceIso (source A ha) (source B hb) :=
  SourceIso.of_pattern (canonicalWhole f) (canonicalWhole_pattern f ha hb)

@[simp] theorem canonicalSourceIso_whole (f : Canonical.Iso A B)
    (ha : SameSortSymmetric A) (hb : SameSortSymmetric B) :
    (canonicalSourceIso f ha hb).whole = canonicalWhole f :=
  SourceIso.of_pattern_whole _ _

end
end CCO.FullPhaseLift.Full
