import CCO.FullPhaseLift.BinarySource.MarkedComparisonSupport
import CCO.FullPhaseLift.Canonical.UnaryExpansion
import CCO.PairHomogeneity

/-! Literal old canonical pair codes and endpoint bits are exactly the
new canonical binary names. Whole binary motions therefore preserve the
actual coded marked table, without asserting any higher relation motion. -/

universe v t
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter OwnerTransversal.CountableColour
noncomputable section

def codeTable {L : Signature} {M : Type v} (T : BoolTable L M) (bits : M → Bit) :
    Table (Profile L 1 × Bit)
      (Profile L 1 × Profile L 1 × Option (Profile L 2)) M where
  owner x := (unaryProfile T x,bits x)
  colour := pairNameCode T

theorem pairNameCode_embedding {L : Signature} {V : Type*} {W : Type*}
    {A : BoolTable L V} {B : BoolTable L W} (e : Canonical.Embedding A B) (x y : V) :
    pairNameCode B (e.point x) (e.point y) = pairNameCode A x y := by
  classical
  simp only [pairNameCode,unaryProfile_embedding,pairProfile_embedding,e.injective.eq_iff]

theorem codeTable_motions {L : Signature} {M : Type v}
    (T : BoolTable L M) (bits : M → Bit)
    (hsym : SameSortSymmetric (Marked.table T bits))
    {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier (Marked.table T bits) i)]
    (H : HomogeneousSource (source (Marked.table T bits) hsym) G) :
    TupleMotions (codeTable T bits) := by
  intro n p q ho hc
  let E := Marked.table T bits
  have hnew (x y : Fin n) : pairNameCode E (p x) (p y) = pairNameCode E (q x) (q y) :=
    (marked_pairNameCode_eq_iff T T bits bits _ _ _ _).mpr
      ⟨hc x y,congrArg Prod.snd (ho x),congrArg Prod.snd (ho y)⟩
  have hcan (x y : Fin n) :
      taggedColour (source E hsym) (pack E (p x)) (pack E (p y)) =
        taggedColour (source E hsym) (pack E (q x)) (pack E (q y)) := by
    apply tagCode_injective E
    rw [tagCode_pack_eq_pairNameCode,tagCode_pack_eq_pairNameCode]
    exact hnew x y
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun x : ULift.{v} (Fin n) => pack E (p x.down))
    (fun x : ULift.{v} (Fin n) => pack E (q x.down))
    (fun x y => hcan x.down y.down)
  let e : M ≃ M := ((pack E).trans (MulAction.toPerm g)).trans (pack E).symm
  have image (x : M) : pack E (e x) = g • pack E x :=
    (pack E).apply_symm_apply _
  have codes (x y : M) : pairNameCode E (e x) (e y) = pairNameCode E x y := by
    have h := congrArg (tagCode E) (H.preserves_colours g (pack E x) (pack E y))
    rw [← image,← image,tagCode_pack_eq_pairNameCode,tagCode_pack_eq_pairNameCode] at h
    exact h
  have old (x y : M) : pairNameCode T (e x) (e y) = pairNameCode T x y ∧
      bits (e x) = bits x ∧ bits (e y) = bits y :=
    (marked_pairNameCode_eq_iff T T bits bits _ _ _ _).mp (codes x y)
  refine ⟨e,?_,?_,?_⟩
  · intro x
    change (unaryProfile T (e x),bits (e x)) = (unaryProfile T x,bits x)
    exact Prod.ext (congrArg (fun c : Profile L 1 × Profile L 1 × Option (Profile L 2) => c.1)
      (old x x).1) (old x x).2.1
  · intro x y
    exact (old x y).1
  · intro x
    apply (pack E).injective
    exact (image (p x)).trans (hg (ULift.up x))

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
