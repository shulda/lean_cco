import CCO.UnaryHN.UnaryFunctions
import PartiteConstruction.Functional.WeakAttachment

/-! Restriction and gluing on the EXACT closed source carrier. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {H E F C X : Type v}
variable {Root : Structure L H} {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

theorem free_commute (hFree : IsFreeAmalgam sL sR iL iR) (z : H) :
    iL (sL z) = iR (sR z) :=
  (hFree.overlap _ _).mpr ⟨z, rfl, rfl⟩

theorem free_fold (hFree : IsFreeAmalgam sL sR iL iR)
    (qL : E → X) (qR : F → X)
    (hAgree : ∀ z, qL (sL z) = qR (sR z)) :
    ∃ p : C → X, (∀ x, p (iL x) = qL x) ∧ (∀ y, p (iR y) = qR y) := by
  classical
  let p : C → X := fun z =>
    if h : ∃ x, z = iL x then qL (Classical.choose h)
    else qR (Classical.choose ((hFree.covers z).resolve_left h))
  have hLeft : ∀ x, p (iL x) = qL x := by
    intro x
    have h : ∃ y, iL x = iL y := ⟨x, rfl⟩
    simp only [p, dite_eq_left h]
    exact congrArg qL (iL.injective (Classical.choose_spec h).symm)
  refine ⟨p, hLeft, ?_⟩
  intro y
  by_cases h : ∃ x, iR y = iL x
  · obtain ⟨x, hx⟩ := h
    obtain ⟨z, hzL, hzR⟩ := (hFree.overlap x y).mp hx.symm
    calc
      p (iR y) = p (iL x) := congrArg p hx
      _ = qL x := hLeft x
      _ = qR y := by rw [hzL, hzR]; exact hAgree z
  · simp only [p, dite_eq_right h]
    exact congrArg qR
      (iR.injective (Classical.choose_spec ((hFree.covers (iR y)).resolve_left h)).symm)

def restrict_embedding {V W : Type v} {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) (S : Set V) (hS : A.IsClosed S)
    (T : Set W) (hT : B.IsClosed T) (hST : ∀ x ∈ S, e x ∈ T) :
    Embedding (A.induce S hS) (B.induce T hT) :=
  embedding_codRestrict (e.comp (inclusion A S hS)) T hT (fun x => hST x x.2)

namespace ClosedRestriction

variable (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) (hS : Whole.IsClosed S)

def leftSet : Set E := {x | iL x ∈ S}
def rightSet : Set F := {y | iR y ∈ S}
def rootSet : Set H := {z | iL (sL z) ∈ S}

include hS

theorem leftClosed : Left.IsClosed (leftSet (iL := iL) S) :=
  iL.preimage_isClosed S hS
theorem rightClosed : Right.IsClosed (rightSet (iR := iR) S) :=
  iR.preimage_isClosed S hS
theorem rootClosed : Root.IsClosed (rootSet (sL := sL) (iL := iL) S) :=
  (iL.comp sL).preimage_isClosed S hS

abbrev root := Root.induce (rootSet (sL := sL) (iL := iL) S) (rootClosed (sL := sL) (iL := iL) S hS)
abbrev left := Left.induce (leftSet (iL := iL) S) (leftClosed (iL := iL) S hS)
abbrev right := Right.induce (rightSet (iR := iR) S) (rightClosed (iR := iR) S hS)
abbrev whole := Whole.induce S hS

def toLeft : Embedding (root (sL := sL) (iL := iL) S hS) (left (iL := iL) S hS) :=
  restrict_embedding sL _ (rootClosed (sL := sL) (iL := iL) S hS) _ (leftClosed (iL := iL) S hS) (fun _ hx => hx)

def toRight : Embedding (root (sL := sL) (iL := iL) S hS) (right (iR := iR) S hS) :=
  restrict_embedding sR _ (rootClosed (sL := sL) (iL := iL) S hS) _ (rightClosed (iR := iR) S hS) (by
    intro z hz
    change iR (sR z) ∈ S
    rw [← free_commute hFree z]
    exact hz)

def leftIn : Embedding (left (iL := iL) S hS) (whole S hS) :=
  restrict_embedding iL _ (leftClosed (iL := iL) S hS) S hS (fun _ hx => hx)

def rightIn : Embedding (right (iR := iR) S hS) (whole S hS) :=
  restrict_embedding iR _ (rightClosed (iR := iR) S hS) S hS (fun _ hx => hx)

theorem free : IsFreeAmalgam (toLeft (sL := sL) (iL := iL) S hS) (toRight hFree S hS)
    (leftIn (iL := iL) S hS) (rightIn (iR := iR) S hS) := by
  constructor
  · intro z
    rcases hFree.covers z.val with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨⟨x, by change iL x ∈ S; exact hx ▸ z.2⟩, Subtype.ext hx⟩
    · exact Or.inr ⟨⟨y, by change iR y ∈ S; exact hy ▸ z.2⟩, Subtype.ext hy⟩
  · intro x y
    constructor
    · intro h
      obtain ⟨z, hzL, hzR⟩ := (hFree.overlap x.val y.val).mp (congrArg Subtype.val h)
      have hz : iL (sL z) ∈ S := hzL ▸ x.2
      exact ⟨⟨z, hz⟩, Subtype.ext hzL, Subtype.ext hzR⟩
    · rintro ⟨z, rfl, rfl⟩
      exact Subtype.ext (free_commute hFree z.val)
  · intro R z
    change Whole.rel R (Subtype.val ∘ z) ↔ _
    rw [hFree.rel_iff]
    constructor
    · rintro (⟨x, hx, heq⟩ | ⟨y, hy, heq⟩)
      · have hxs : ∀ j, iL (x j) ∈ S := fun j => by
          have h : (z j).val = _ := congrFun heq j
          exact (congrArg (fun t : C => t ∈ S) h).mp (z j).2
        let xx : Fin (L.relArity R) → leftSet (iL := iL) S := fun j => ⟨x j, hxs j⟩
        exact Or.inl ⟨xx, hx, funext (fun j => Subtype.ext (congrFun heq j))⟩
      · have hys : ∀ j, iR (y j) ∈ S := fun j => by
          have h : (z j).val = _ := congrFun heq j
          exact (congrArg (fun t : C => t ∈ S) h).mp (z j).2
        let yy : Fin (L.relArity R) → rightSet (iR := iR) S := fun j => ⟨y j, hys j⟩
        exact Or.inr ⟨yy, hy, funext (fun j => Subtype.ext (congrFun heq j))⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨Subtype.val ∘ x, hx, rfl⟩
      · exact Or.inr ⟨Subtype.val ∘ y, hy, rfl⟩
  · intro F z out
    change out.val ∈ Whole.func F (Subtype.val ∘ z) ↔ _
    rw [hFree.func_iff]
    constructor
    · rintro (⟨x, y, hy, hArgs, hOut⟩ | ⟨x, y, hy, hArgs, hOut⟩)
      · have hxs : ∀ j, iL (x j) ∈ S := fun j => by
          have h : (z j).val = _ := congrFun hArgs j
          exact (congrArg (fun t : C => t ∈ S) h).mp (z j).2
        have hys : iL y ∈ S := hOut ▸ out.2
        let xx : Fin (L.funcArity F) → leftSet (iL := iL) S := fun j => ⟨x j, hxs j⟩
        exact Or.inl ⟨xx, ⟨y, hys⟩, hy,
          funext (fun j => Subtype.ext (congrFun hArgs j)), Subtype.ext hOut⟩
      · have hxs : ∀ j, iR (x j) ∈ S := fun j => by
          have h : (z j).val = _ := congrFun hArgs j
          exact (congrArg (fun t : C => t ∈ S) h).mp (z j).2
        have hys : iR y ∈ S := hOut ▸ out.2
        let xx : Fin (L.funcArity F) → rightSet (iR := iR) S := fun j => ⟨x j, hxs j⟩
        exact Or.inr ⟨xx, ⟨y, hys⟩, hy,
          funext (fun j => Subtype.ext (congrFun hArgs j)), Subtype.ext hOut⟩
    · rintro (⟨x, y, hy, rfl, rfl⟩ | ⟨x, y, hy, rfl, rfl⟩)
      · exact Or.inl ⟨Subtype.val ∘ x, y.val, hy, rfl, rfl⟩
      · exact Or.inr ⟨Subtype.val ∘ x, y.val, hy, rfl, rfl⟩

end ClosedRestriction

theorem free_completion_glue (hFree : IsFreeAmalgam sL sR iL iR)
    {Target : Structure L X} (qL : E → X) (qR : F → X)
    (hL : HE Left Target qL) (hR : HE Right Target qR)
    (hAgree : ∀ z, qL (sL z) = qR (sR z)) :
    ∃ p : C → X, HE Whole Target p ∧
      (∀ x, p (iL x) = qL x) ∧ (∀ y, p (iR y) = qR y) := by
  obtain ⟨p, hpL, hpR⟩ := free_fold hFree qL qR hAgree
  exact ⟨p, IsEHNHomomorphismEmbedding.of_freeAmalgam hFree hL hR hpL hpR, hpL, hpR⟩

end CCO.UnaryHN.Native
