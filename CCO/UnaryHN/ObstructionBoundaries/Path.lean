import CCO.UnaryHN.ObstructionBoundaries.Basic
import Lean.Elab.Tactic.Omega

/-! An actual unbounded family: the R-path 0--1--...--(n-1), with a
positive B-edge between its endpoints. No homomorphism to any equivalence
network exists, so in particular there is no homomorphism-embedding completion. -/
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

def Adjacent {n : ℕ} (x y : Fin n) : Prop := x.val + 1 = y.val ∨ y.val + 1 = x.val

def Endpoints {n : ℕ} (x y : Fin n) : Prop :=
  (x.val = 0 ∧ y.val + 1 = n) ∨ (y.val = 0 ∧ x.val + 1 = n)

def path (n : ℕ) : Diagram (Fin n) where
  rel color xs := if color then Endpoints (xs 0) (xs 1) else Adjacent (xs 0) (xs 1)
  func F := Empty.elim F

theorem adjacent_symm {n : ℕ} {x y : Fin n} (h : Adjacent x y) : Adjacent y x := h.symm

theorem endpoints_symm {n : ℕ} {x y : Fin n} (h : Endpoints x y) : Endpoints y x := h.symm

theorem path_irreflexive {n : ℕ} (hn : 2 ≤ n) (color : Bool) (x : Fin n) :
    ¬ (path n).rel color ![x, x] := by
  cases color <;> change ¬ _ <;> simp only [path, Bool.false_eq_true, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  · unfold Adjacent
    omega
  · unfold Endpoints
    omega

/-- The contradiction uses only the positive homomorphism laws; global
injectivity and protected irreducible tests are not needed. -/
theorem path_no_homomorphism {n : ℕ} (hn : 2 ≤ n) {V : Type*}
    (E : Setoid V) (f : Fin n → V)
    (hf : (path n).IsHomomorphism (network E) f) : False := by
  let z : Fin n := ⟨0, by omega⟩
  have chain : ∀ k, ∀ hk : k < n, E.r (f z) (f ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact E.refl (f z)
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hEdge : (path n).rel false ![⟨k, hkn⟩, ⟨k + 1, hk⟩] := by
        exact Or.inl rfl
      have hImage := hf.1 false ![⟨k, hkn⟩, ⟨k + 1, hk⟩] hEdge
      exact E.trans (ih hkn) hImage.1
  let t : Fin n := ⟨n - 1, by omega⟩
  have hEnd : (path n).rel true ![z, t] := by
    change (0 = 0 ∧ n - 1 + 1 = n) ∨ _
    exact Or.inl ⟨rfl, by omega⟩
  have hDifferent := hf.1 true ![z, t] hEnd
  exact hDifferent (chain (n - 1) (by omega))

theorem path_no_completion {n : ℕ} (hn : 2 ≤ n) : ¬ HasCompletion completed (path n) := by
  rintro ⟨V, _, D, ⟨_, E, rfl⟩, f, hf⟩
  exact path_no_homomorphism hn E f ⟨hf.1.1, fun F => Empty.elim F⟩

end CCO.UnaryHN.Native.ObstructionBoundaries
