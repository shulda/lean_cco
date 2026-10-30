import CCO.APCharacter.Masks
import Lean.Elab.Tactic.Omega

/-! Only consecutive pairs are specified. The actual witness tuple is
metadata and never fills a chord or the root pair of this partial path. -/
universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

def Adjacent {n : ℕ} (p q : Fin (n+1)) : Prop := p.val+1 = q.val ∨ q.val+1 = p.val

theorem adjacent_symm {n : ℕ} {p q : Fin (n+1)} : Adjacent p q ↔ Adjacent q p :=
  or_comm

noncomputable def binaryPath {n : ℕ} (point : Fin (n+1) → Sigma X) :
    PartialDiagram S (Fin (n+1)) := by
  classical
  exact {
    finite_type := inferInstance
    vertexSort p := (point p).1
    edge p q _ := if Adjacent p q then S.colour (point p).2 (point q).2 else none
    edge_reverse := by
      intro p q hpq a
      by_cases h : Adjacent p q
      · have h' := adjacent_symm.mp h
        simp only [if_pos h,if_pos h']
        exact S.colour_swap (point p).2 (point q).2 a
      · have h' : ¬Adjacent q p := fun he => h (adjacent_symm.mpr he)
        simp only [if_neg h,if_neg h',reduceCtorEq] }

theorem binaryPath_edge {n : ℕ} (point : Fin (n+1) → Sigma X)
    (p q : Fin (n+1)) (hne : p ≠ q) (h : Adjacent p q) :
    (binaryPath (S := S) point).edge p q hne = S.colour (point p).2 (point q).2 := by
  classical
  exact if_pos h

theorem binaryPath_root_unspecified {n : ℕ} (point : Fin (n+1) → Sigma X)
    (hn : 2 ≤ n) (hne : (0 : Fin (n+1)) ≠ Fin.last n) :
    (binaryPath (S := S) point).edge 0 (Fin.last n) hne = none := by
  classical
  have hnot : ¬Adjacent (0 : Fin (n+1)) (Fin.last n) := by
    change ¬(0+1 = n ∨ n+1 = 0)
    omega
  exact if_neg hnot

def binaryPath_realization {n : ℕ} (point : Fin (n+1) → Sigma X) :
    DiagramHom (binaryPath (S := S) point) where
  point p := (point p).2
  preserves_edge := by
    intro p q hpq a ha
    classical
    change (if Adjacent p q then S.colour (point p).2 (point q).2 else none) = some a at ha
    split at ha
    · exact ha
    · cases ha

theorem binaryPath_injective {n : ℕ} (point : Fin (n+1) → Sigma X)
    (hi : Function.Injective point) : (binaryPath_realization (S := S) point).IsInjective := hi

theorem binaryPath_legal {n : ℕ} (point : Fin (n+1) → Sigma X)
    (M : MaskData S) (mark : Sigma X → Bit) (hm : M.GlobalMarking mark) :
    M.LocalLegal (binaryPath (S := S) point) (mark ∘ point) := by
  constructor
  · intro p
    exact hm.1 (point p)
  · intro p q hpq a ha
    have hh := (binaryPath_realization (S := S) point).preserves_edge p q hpq a ha
    change S.colour (point p).2 (point q).2 = some a at hh
    have h := hm.2 (point p) (point q)
    rwa [hh] at h

end CCO.FullPhaseLift.Detours
