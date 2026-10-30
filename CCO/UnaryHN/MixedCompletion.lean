import CCO.UnaryHN.ClosedAmalgam
import CCO.UnaryHN.ClosedLocal
import CCO.UnaryHN.MarkedCompletion

/-! The genuine class-dependent mixed step. The two literal closed projected
side images are smaller. Their ordinary K-completions are extended to the
SAME full A mark using actual K-SAP, then glued over that mark. This avoids
the stronger, unresolved universal strict-tree extension assertion. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {K : Class.{u,v} L}

theorem side_image_budget {E C P : Type v} [Fintype E]
    [DecidableEq C] [DecidableEq P]
    (i : E → C) (hi : Function.Injective i) (p : C → P)
    (S : Finset C) (m : ℕ) (hS : S.card ≤ m + 1)
    (hOutside : ∃ z ∈ S, ∀ x, z ≠ i x) :
    (((Finset.univ : Finset E).filter (fun x => i x ∈ S)).image (p ∘ i)).card ≤ m := by
  classical
  let B := (Finset.univ : Finset E).filter (fun x => i x ∈ S)
  let T := B.image i
  have hSub : T ⊆ S := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2
  have hNe : T ≠ S := by
    intro hEq
    obtain ⟨z, hz, hNot⟩ := hOutside
    have hzT : z ∈ T := by rw [hEq]; exact hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hzT
    exact hNot x hx.symm
  have hLt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩)
  have hCard : T.card = B.card := Finset.card_image_of_injective B hi
  have hBound : (B.image (p ∘ i)).card ≤ B.card := Finset.card_image_le
  change (B.image (p ∘ i)).card ≤ m
  omega

theorem side_completion_with_A_mark (hK : FiniteHereditarySAP K)
    (hIrr : AllIrreducible K) {U V P : Type v}
    {A : Structure L U} {Side : Structure L V} {D : Structure L P}
    (hA : K A) (alpha : Embedding A D) (p : V → P) (hp : HE Side D p)
    (S : Set V) (hS : Side.IsClosed S) (I : Finset P) (hI : D.IsClosed (↑I : Set P))
    (hImage : (↑I : Set P) = p '' S) (hComp : HasCompletion K (D.induce (↑I : Set P) hI)) :
    ∃ (X : Type v) (_ : Finite X) (Target : Structure L X), K Target ∧
      ∃ (f : S → X) (mark : Embedding A Target),
        HE (Side.induce S hS) Target f ∧
        ∀ (x : S) (a : U), p x.val = alpha a → f x = mark a := by
  let R : Set U := {a | alpha a ∈ (↑I : Set P)}
  have hR : A.IsClosed R := alpha.preimage_isClosed (↑I : Set P) hI
  let rA : Embedding (A.induce R hR) A := inclusion A R hR
  let rI : Embedding (A.induce R hR) (D.induce (↑I : Set P) hI) :=
    restrict_embedding alpha R hR (↑I : Set P) hI (fun _ ha => ha)
  obtain ⟨X, hX, Target, hTarget, g, mark, hg, hMark⟩ :=
    completion_with_mark hK hIrr hA rI rA hComp
  have hRange : ∀ x : S, p x.val ∈ (↑I : Set P) := by
    intro x
    rw [hImage]
    exact ⟨x.val, x.2, rfl⟩
  let pS : S → (↑I : Set P) := fun x => ⟨p x.val, hRange x⟩
  have hpS : HE (Side.induce S hS) (D.induce (↑I : Set P) hI) pS :=
    HE.codRestrict (hp.comp (inclusion Side S hS).isEHNHomomorphismEmbedding)
      (↑I : Set P) hI hRange
  refine ⟨X, hX, Target, hTarget, g ∘ pS, mark, hg.comp hpS, ?_⟩
  intro x a ha
  have haI : alpha a ∈ (↑I : Set P) := ha ▸ hRange x
  have hEq : pS x = rI ⟨a, haI⟩ := Subtype.ext ha
  exact (congrArg g hEq).trans (hMark ⟨a, haI⟩)

theorem mixed_closed_completion (hK : FiniteHereditarySAP K)
    (hIrr : AllIrreducible K) (hUnary : Unary L)
    {U H E F C P : Type v} [Finite E] [Finite F]
    {A : Structure L U} {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D) (hA : K A)
    (p : C → P) (hp : HE Whole D p)
    (hRoot : ∀ z, ∃ a, p (iL (sL z)) = alpha a)
    (m : ℕ) (hPrev : ClosedSmallCompletable K D m)
    (S : Finset C) (hSize : S.card ≤ m + 1) (hS : Whole.IsClosed (↑S : Set C))
    (hOutsideL : ∃ z ∈ S, ∀ x, z ≠ iL x)
    (hOutsideR : ∃ z ∈ S, ∀ y, z ≠ iR y) :
    HasCompletion K (Whole.induce (↑S : Set C) hS) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  let SL := (Finset.univ : Finset E).filter (fun x => iL x ∈ S)
  let SR := (Finset.univ : Finset F).filter (fun y => iR y ∈ S)
  let IL := SL.image (p ∘ iL)
  let IR := SR.image (p ∘ iR)
  have hSetL : (↑SL : Set E) = {x | iL x ∈ (↑S : Set C)} := by ext x; simp [SL]
  have hSetR : (↑SR : Set F) = {y | iR y ∈ (↑S : Set C)} := by ext y; simp [SR]
  have hImageL : (↑IL : Set P) = (p ∘ iL) '' {x | iL x ∈ (↑S : Set C)} := by
    rw [← hSetL]; ext z; simp [IL]
  have hImageR : (↑IR : Set P) = (p ∘ iR) '' {y | iR y ∈ (↑S : Set C)} := by
    rw [← hSetR]; ext z; simp [IR]
  have hpL : HE Left D (p ∘ iL) := hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : HE Right D (p ∘ iR) := hp.comp iR.isEHNHomomorphismEmbedding
  have hSL := iL.preimage_isClosed (↑S : Set C) hS
  have hSR := iR.preimage_isClosed (↑S : Set C) hS
  have hIL : D.IsClosed (↑IL : Set P) := by
    rw [hImageL]
    exact full_image_closed (hpL.full hUnary) _ hSL
  have hIR : D.IsClosed (↑IR : Set P) := by
    rw [hImageR]
    exact full_image_closed (hpR.full hUnary) _ hSR
  have hCardL : IL.card ≤ m := side_image_budget iL iL.injective p S m hSize hOutsideL
  have hCardR : IR.card ≤ m := side_image_budget iR iR.injective p S m hSize hOutsideR
  obtain ⟨XL, hXL, TL, hTL, fL, markL, hfL, hMarkL⟩ :=
    side_completion_with_A_mark hK hIrr hA alpha (p ∘ iL) hpL
      _ hSL IL hIL hImageL (hPrev IL hCardL hIL)
  obtain ⟨XR, hXR, TR, hTR, fR, markR, hfR, hMarkR⟩ :=
    side_completion_with_A_mark hK hIrr hA alpha (p ∘ iR) hpR
      _ hSR IR hIR hImageR (hPrev IR hCardR hIR)
  obtain ⟨X, hX, T, hT, jL, jR, hAgree, _⟩ := hK.strong hTL hTR markL markR
  let qL := jL ∘ fL
  let qR := jR ∘ fR
  have hCompL := jL.isEHNHomomorphismEmbedding.comp hfL
  have hCompR := jR.isEHNHomomorphismEmbedding.comp hfR
  have hCompat : ∀ z,
      qL (ClosedRestriction.toLeft (sL := sL) (iL := iL) (↑S : Set C) hS z) =
      qR (ClosedRestriction.toRight hFree (↑S : Set C) hS z) := by
    intro z
    obtain ⟨a, ha⟩ := hRoot z.val
    have haR : p (iR (sR z.val)) = alpha a := by
      rw [← free_commute hFree z.val]
      exact ha
    exact (congrArg jL (hMarkL (ClosedRestriction.toLeft (sL := sL) (iL := iL) (↑S : Set C) hS z) a ha)).trans
      ((hAgree a).trans (congrArg jR (hMarkR (ClosedRestriction.toRight hFree (↑S : Set C) hS z) a haR)).symm)
  obtain ⟨f, hf, _, _⟩ := free_completion_glue
    (ClosedRestriction.free hFree (↑S : Set C) hS) qL qR hCompL hCompR hCompat
  exact ⟨X, hX, T, hT, f, hf⟩

end CCO.UnaryHN.Native
