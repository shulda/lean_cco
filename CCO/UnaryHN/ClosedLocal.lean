import CCO.UnaryHN.UnaryFunctions
import PartiteConstruction.Functional.WeakOperations

/-! Literal closed-image pullback, with no hull-size replacement. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {K : Class.{u,v} L} {V W : Type v}

theorem ClosedSmallCompletable.mono {C : Structure L V} {m n : ℕ}
    (h : ClosedSmallCompletable K C n) (hmn : m ≤ n) :
    ClosedSmallCompletable K C m :=
  fun S hS hClosed => h S (hS.trans hmn) hClosed

theorem ClosedSmallCompletable.pullback_unary (hUnary : Unary L)
    {C : Structure L V} {D : Structure L W} {p : V → W} (hp : HE C D p)
    {n : ℕ} (hD : ClosedSmallCompletable K D n) : ClosedSmallCompletable K C n := by
  classical
  intro S hS hClosed
  let I := S.image p
  have hImage : (↑I : Set W) = p '' (↑S : Set V) := by ext y; simp [I]
  have hI : D.IsClosed (↑I : Set W) := by
    rw [hImage]
    exact full_image_closed (hp.full hUnary) _ hClosed
  have hRange : ∀ x : (↑S : Set V), p x.val ∈ (↑I : Set W) := by
    intro x
    exact Finset.mem_image.mpr ⟨x.val, x.2, rfl⟩
  have hpS : HE (C.induce (↑S : Set V) hClosed) D (p ∘ Subtype.val) :=
    hp.comp (inclusion C (↑S : Set V) hClosed).isEHNHomomorphismEmbedding
  exact HasCompletion.pullback (hpS.codRestrict (↑I : Set W) hI hRange)
    (hD I ((Finset.card_image_le).trans hS) hI)

theorem closed_small_of_completion {C : Structure L V}
    (hC : HasCompletion K C) (n : ℕ) : ClosedSmallCompletable K C n :=
  fun S _ hS => hC.of_embedding (inclusion C (↑S : Set V) hS)

theorem closed_small_zero_of_placement (hK : FiniteHereditarySAP K)
    {C : Structure L V} {B : Structure L W} (hB : K B) (eB : Embedding B C) :
    ClosedSmallCompletable K C 0 := by
  classical
  intro S hS hClosed
  have hEmpty : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
  have hRange : ∀ x : (↑S : Set V), ∃ y : W,
      (inclusion C (↑S : Set V) hClosed) x = eB y := by
    intro x
    have hNone : ∀ z : V, z ∉ S := by intro z; rw [hEmpty]; exact Finset.notMem_empty z
    exact (hNone x.val x.2).elim
  exact (HasCompletion.of_mem hK hB).of_embedding
    ((inclusion C (↑S : Set V) hClosed).factorThroughClosedRange eB hRange)

end CCO.UnaryHN.Native
