import CCO.APRamseyReadout.SortBlockNormalizer
import CCO.FullCode.Consumer

/-! Block codes retain within-HIDDEN-target comparisons. Different
visible tags are irrelevant to this criterion. The omitted comparisons
are reconstructed from actual presentation domains and fixed sort priority. -/

universe u v w a b
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable (priority : LinearOrder L.Sorts)
variable {C : Structure (blockLanguage L) V} {D : Structure (blockLanguage L) W}
variable {S : RootScheme (blockLanguage L)} (N : NormalForms (blockLanguage L))

/-- Presentation output sorts constrain EVERY literal order symbol. -/
theorem blockOrderCode_sorts (r s : Root C S) (p q : Presentation N S)
    (i j : L.Sorts) (h : BinaryCode N (.inr (i,j)) r s p q) : p.2.1 = i ∧ q.2.1 = j := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h
  have hs := C.binary_sorted (.inr (i,j)) x y hxy
  exact ⟨(r.presentation_sorted N p hx).symm.trans hs.1,
    (s.presentation_sorted N q hy).symm.trans hs.2⟩

/-- Applicability is explicit: a missing term presentation makes the
comparison false even when the priority orders its target sorts. -/
theorem blockOrderCode_different (fixed : blockNormalize L priority C = C)
    (r s : Root C S) (p q : Presentation N S) (i j : L.Sorts) (hne : i ≠ j) :
    BinaryCode N (.inr (i,j)) r s p q ↔
      (r.presentation N p).Nonempty ∧ (s.presentation N q).Nonempty ∧
        p.2.1 = i ∧ q.2.1 = j ∧ @LT.lt _ priority.toLT i j := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    have ht := blockOrderCode_sorts N r s p q i j ⟨x,y,hx,hy,hxy⟩
    have hb : (blockNormalize L priority C).binary (.inr (i,j)) x y := fixed.symm ▸ hxy
    change C.sort x = i ∧ C.sort y = j ∧
      (@LT.lt _ priority.toLT i j ∨ (i = j ∧ C.binary (.inr (i,j)) x y)) at hb
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,ht.1,ht.2,hb.2.2.elim id (fun h => False.elim (hne h.1))⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩,hi,hj,hpriority⟩
    refine ⟨x,y,hx,hy,?_⟩
    have hb : (blockNormalize L priority C).binary (.inr (i,j)) x y :=
      ⟨(r.presentation_sorted N p hx).trans hi,(s.presentation_sorted N q hy).trans hj,
        Or.inl hpriority⟩
    exact fixed ▸ hb

/-- The reduced tests keep every non-order code. The final actual owner
reduction deletes those through their proved old-type definitions. -/
structure WithinTargetEmbedding {A : Type a} {B : Type b}
    (O : Object C S A) (P : Object D S B) where
  point : A → B
  injective : Function.Injective point
  tag_eq : ∀ x, (P.root (point x)).tag = (O.root x).tag
  equality_iff : ∀ x y p q, EqualityCode N (P.root (point x)) (P.root (point y)) p q ↔
    EqualityCode N (O.root x) (O.root y) p q
  unary_iff : ∀ U x p, UnaryCode N U (P.root (point x)) p ↔ UnaryCode N U (O.root x) p
  old_binary_iff : ∀ R x y p q, BinaryCode N (.inl R) (P.root (point x)) (P.root (point y)) p q ↔
    BinaryCode N (.inl R) (O.root x) (O.root y) p q
  within_iff : ∀ i x y p q, BinaryCode N (.inr (i,i)) (P.root (point x)) (P.root (point y)) p q ↔
    BinaryCode N (.inr (i,i)) (O.root x) (O.root y) p q

namespace WithinTargetEmbedding
variable {N} {A : Type a} {B : Type b} {O : Object C S A} {P : Object D S B}

@[ext] theorem ext {f g : WithinTargetEmbedding N O P} (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f; cases g
  have hp := funext h
  cases hp
  rfl

def ofFull (f : Object.Embedding N O P) : WithinTargetEmbedding N O P where
  point := f.point
  injective := f.injective
  tag_eq := f.tag_eq
  equality_iff := f.equality_iff
  unary_iff := f.unary_iff
  old_binary_iff R := f.binary_iff (.inl R)
  within_iff i := f.binary_iff (.inr (i,i))

/-- Every omitted unequal-output-sort test is restored by definedness
and priority. Both directions hold on ALL visible embedding maps. -/
def toFull (fixedC : blockNormalize L priority C = C) (fixedD : blockNormalize L priority D = D)
    (f : WithinTargetEmbedding N O P) : Object.Embedding N O P where
  point := f.point
  injective := f.injective
  tag_eq := f.tag_eq
  equality_iff := f.equality_iff
  unary_iff := f.unary_iff
  binary_iff R x y p q := by
    cases R with
    | inl R => exact f.old_binary_iff R x y p q
    | inr ij =>
      obtain ⟨i,j⟩ := ij
      by_cases he : i = j
      · subst j
        exact f.within_iff i x y p q
      · rw [blockOrderCode_different priority N fixedD,blockOrderCode_different priority N fixedC]
        · have hp : ((P.root (f.point x)).presentation N p).Nonempty ↔
              ((O.root x).presentation N p).Nonempty := by
            rw [← definedness_diagonal N (P.root (f.point x)) p,
              ← definedness_diagonal N (O.root x) p]
            exact f.equality_iff x x p p
          have hq : ((P.root (f.point y)).presentation N q).Nonempty ↔
              ((O.root y).presentation N q).Nonempty := by
            rw [← definedness_diagonal N (P.root (f.point y)) q,
              ← definedness_diagonal N (O.root y) q]
            exact f.equality_iff y y q q
          exact and_congr hp (and_congr hq Iff.rfl)
        · exact he
        · exact he

end WithinTargetEmbedding

/-- Same point maps, with no surjectivity-on-maps or chosen subfamily
of code embeddings hidden in the reduction. -/
def withinTargetEmbeddingEquiv {A : Type a} {B : Type b}
    (O : Object C S A) (P : Object D S B)
    (fixedC : blockNormalize L priority C = C) (fixedD : blockNormalize L priority D = D) :
    WithinTargetEmbedding N O P ≃ Object.Embedding N O P where
  toFun := WithinTargetEmbedding.toFull priority fixedC fixedD
  invFun := WithinTargetEmbedding.ofFull
  left_inv _ := WithinTargetEmbedding.ext (fun _ => rfl)
  right_inv _ := Object.Embedding.ext (fun _ => rfl)

end
end CCO.APRamseyReadout
