import CCO.FullPhaseLift.Canonical.Expansion

/-! Explicit quantifier-free definitions of every added canonical name.
The pair-name formula includes logical inequality; diagonal data remain
in the old signature and in the unary profile. -/

universe v
namespace CCO.FullPhaseLift.Canonical
open FirstOrder FirstOrder.Language

noncomputable def unaryNameFormula {L : Signature} (p : Profile L 1) :
    L.firstOrder.Formula (Fin 1) := profileFormula p

noncomputable def pairNameFormula {L : Signature} (p : Profile L 2) :
    L.firstOrder.Formula (Fin 2) :=
  ((Term.var 0 : L.firstOrder.Term (Fin 2)).equal (.var 1)).not ⊓ profileFormula p

theorem unaryNameFormula_realize {L : Signature} {V : Type v} (T : BoolTable L V)
    (p : Profile L 1) (xs : Fin 1 → V) :
    letI := toFirstOrder T
    (unaryNameFormula p).Realize xs ↔ unaryProfile T (xs 0) = p := by
  classical
  letI := toFirstOrder T
  have ht : xs = fun _ => xs 0 := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj]
  have hp : profile T xs = unaryProfile T (xs 0) := congrArg (profile T) ht
  exact (profileFormula_realize T p xs).trans (by rw [hp])

theorem pairNameFormula_realize {L : Signature} {V : Type v} (T : BoolTable L V)
    (p : Profile L 2) (xs : Fin 2 → V) :
    letI := toFirstOrder T
    (pairNameFormula p).Realize xs ↔ xs 0 ≠ xs 1 ∧ pairProfile T (xs 0) (xs 1) = p := by
  classical
  letI := toFirstOrder T
  have ht : xs = ![xs 0,xs 1] := by
    funext j
    fin_cases j <;> rfl
  simp only [pairNameFormula,Formula.realize_inf,Formula.realize_not,
    Formula.realize_equal,Term.realize,profileFormula_realize]
  have hp : profile T xs = pairProfile T (xs 0) (xs 1) := congrArg (profile T) ht
  rw [hp]

theorem unaryNameFormula_qf {L : Signature} (p : Profile L 1) :
    (unaryNameFormula p).IsQF := profileFormula_qf p

theorem pairNameFormula_qf {L : Signature} (p : Profile L 2) :
    (pairNameFormula p).IsQF :=
  (BoundedFormula.IsAtomic.equal _ _).isQF.not.inf (profileFormula_qf p)

end CCO.FullPhaseLift.Canonical
