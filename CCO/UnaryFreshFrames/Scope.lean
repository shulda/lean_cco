import CCO.UnaryFreshFrames.SAPAlgebraicity

/-! The final source theorem keeps its actual finite-language, countable,
oligomorphic homogeneous scope. The stronger construction lemmas above do not
need these extra conditions; none of them substitutes a desired conclusion. -/
universe u v
namespace CCO.UnaryFreshFrames

def Language.FiniteNamed (L : Language.{u}) : Prop :=
  Finite L.Sorts ∧ Finite L.Func ∧ Finite L.Rel

namespace Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

def tupleOrbit (n : ℕ) : Setoid (Fin n → V) where
  r xs ys := ∃ g : H.Aut, ∀ i, g • xs i = ys i
  iseqv := ⟨fun _ => ⟨1, fun _ => one_smul _ _⟩,
    by
      rintro xs ys ⟨g, hg⟩
      exact ⟨g⁻¹, fun i => by rw [← hg i, inv_smul_smul]⟩,
    by
      rintro xs ys zs ⟨g, hg⟩ ⟨h, hh⟩
      exact ⟨h * g, fun i => by rw [mul_smul, hg i, hh i]⟩⟩

/-- Actual finiteness of the full named-Aut orbits on every finite tuple power. -/
def Oligomorphic : Prop := ∀ n : ℕ, Finite (_root_.Quotient (H.tupleOrbit n))

structure FinalScope : Prop where
  countable : Countable V
  finiteLanguage : L.FiniteNamed
  oligomorphic : H.Oligomorphic
  homogeneous : H.Homogeneous
  locallyFinite : H.LocallyFinite

end Structure
end CCO.UnaryFreshFrames
