import CCO.SIR.Positive.Menus
import CCO.SpanEmbedding

/-!
# Actual exact base-span menus and onto-base selected naturality

Formal base indices may live in any universe. Their actual finite image is
exactly the base used by the SIR menu, so original exactness is proved, rather
than an extra premise of naturality. Onto the WHOLE designated target base is
part of the actual factor-embedding interface.
-/

universe u v w z z'

namespace CCO.SIR.Positive

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)] {i j : ι} {C : Type z}

noncomputable def realBaseFinset (A : S.ActualSpan (i := i) (j := j) C) :
    Finset (Sigma X) := A.baseVertices_finite.toFinset

@[simp] theorem mem_realBaseFinset (A : S.ActualSpan (i := i) (j := j) C)
    (x : Sigma X) : x ∈ realBaseFinset S A ↔ x ∈ A.baseVertices := by
  exact Set.Finite.mem_toFinset _

theorem actualSpan_menu_eq (A : S.ActualSpan (i := i) (j := j) C) :
    A.menu = baseMenu S (realBaseFinset S A) ⟨i,A.left⟩ ⟨j,A.right⟩ := by
  ext a
  constructor
  · intro ha x hx
    obtain ⟨c,rfl⟩ := (mem_realBaseFinset S A x).mp hx
    change a ∈ S.product (edgeMenu S ⟨i,A.left⟩ ⟨A.baseSort c,A.point c⟩)
      (edgeMenu S ⟨A.baseSort c,A.point c⟩ ⟨j,A.right⟩)
    rw [edgeMenu_of_colour S (A.leftColour c), edgeMenu_of_colour S (A.rightColour c)]
    exact ha c
  · intro ha c
    have hx : (⟨A.baseSort c,A.point c⟩ : Sigma X) ∈ realBaseFinset S A :=
      (mem_realBaseFinset S A _).mpr ⟨c,rfl⟩
    have hh := ha _ hx
    change a ∈ S.product (edgeMenu S ⟨i,A.left⟩ ⟨A.baseSort c,A.point c⟩)
      (edgeMenu S ⟨A.baseSort c,A.point c⟩ ⟨j,A.right⟩) at hh
    rw [edgeMenu_of_colour S (A.leftColour c), edgeMenu_of_colour S (A.rightColour c)] at hh
    exact hh

theorem actualSpan_menu_exact (K : Selectors.ExactCalculus S)
    (A : S.ActualSpan (i := i) (j := j) C) : StrongExact.Exact S A.menu := by
  rw [actualSpan_menu_eq S A]
  exact baseMenu_exact S K _
    (fun hc => A.leftRoot_not_base ((mem_realBaseFinset S A _).mp hc))
    (fun hc => A.rightRoot_not_base ((mem_realBaseFinset S A _).mp hc)) A.distinctRoots

theorem selected_factor_naturality (K : Selectors.ExactCalculus S)
    (h : Selectors.HereditarySelector S) {D : Type z'}
    (A : S.ActualSpan (i := i) (j := j) C)
    (B : S.ActualSpan (i := i) (j := j) D)
    {LeftSrc RightSrc LeftDst RightDst : FiniteInduced (X := X)}
    (e : S.FactorSpanEmbedding A B LeftSrc RightSrc LeftDst RightDst) :
    h.choose A.menu (actualSpan_menu_exact S K A) =
      h.choose B.menu (actualSpan_menu_exact S K B) := by
  have hc : ∀ (M N : S.Menu i j) (hM : StrongExact.Exact S M)
      (hN : StrongExact.Exact S N), M = N → h.choose M hM = h.choose N hN := by
    intro M N hM hN hm
    cases hm
    rfl
  exact hc _ _ _ _ e.menu_preserved

end CCO.SIR.Positive
