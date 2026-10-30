import CCO.FullPhaseLift.Canonical.FirstOrder
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Finite complete quantifier-free profiles. All original relation tuples
on the named slots are tested; repeated coordinates and nullaries occur
literally in `AtomicTest`. -/

universe v w
namespace CCO.FullPhaseLift.Canonical
open FirstOrder FirstOrder.Language

def unaryProfile {L : Signature} {V : Type v} (T : BoolTable L V) (x : V) :
    Profile L 1 := profile T (fun _ => x)

def pairProfile {L : Signature} {V : Type v} (T : BoolTable L V) (x y : V) :
    Profile L 2 := profile T ![x,y]

def swapProfile {L : Signature} (p : Profile L 2) : Profile L 2 :=
  fun a => p ⟨a.1, Fin.rev ∘ a.2⟩

def diagonalProfile {L : Signature} (p : Profile L 1) : Profile L 2 :=
  fun a => p ⟨a.1,fun _ => 0⟩

@[simp] theorem pairProfile_self {L : Signature} {V : Type v}
    (T : BoolTable L V) (x : V) :
    pairProfile T x x = diagonalProfile (unaryProfile T x) := by
  funext a
  apply congrArg (T a.1)
  funext j
  change ![x,x] (a.2 j) = x
  generalize a.2 j = h
  fin_cases h <;> rfl

@[simp] theorem swapProfile_swap {L : Signature} (p : Profile L 2) :
    swapProfile (swapProfile p) = p := by
  funext a
  simp [swapProfile,Function.comp_def]

@[simp] theorem pairProfile_swap {L : Signature} {V : Type v}
    (T : BoolTable L V) (x y : V) :
    swapProfile (pairProfile T x y) = pairProfile T y x := by
  funext a
  apply congrArg (T a.1)
  funext k
  change ![x,y] (Fin.rev (a.2 k)) = ![y,x] (a.2 k)
  generalize a.2 k = h
  fin_cases h <;> rfl

@[simp] theorem unaryProfile_embedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B) (x : V) :
    unaryProfile B (e.point x) = unaryProfile A x := profile_embedding e _

@[simp] theorem pairProfile_embedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B) (x y : V) :
    pairProfile B (e.point x) (e.point y) = pairProfile A x y := by
  have h : e.point ∘ ![x,y] = ![e.point x,e.point y] := by
    funext j
    fin_cases j <;> rfl
  simpa only [h,pairProfile] using profile_embedding e ![x,y]

noncomputable def profileFormula {L : Signature} {k : ℕ} (p : Profile L k) :
    L.firstOrder.Formula (Fin k) :=
  Formula.iInf fun a : AtomicTest L k =>
    let atom := Relations.formula (L := L.firstOrder) ⟨a.1,rfl⟩
      (fun j => .var (a.2 j))
    if p a then atom else atom.not

theorem profileFormula_realize {L : Signature} {V : Type v}
    (T : BoolTable L V) {k : ℕ} (p : Profile L k) (xs : Fin k → V) :
    letI := toFirstOrder T
    (profileFormula p).Realize xs ↔ profile T xs = p := by
  classical
  letI := toFirstOrder T
  simp only [profileFormula,Formula.realize_iInf]
  rw [funext_iff]
  apply forall_congr'
  intro a
  cases hp : p a
  · simp only [hp, Bool.false_eq_true, reduceIte, Formula.realize_not]
    change (¬T a.1 (xs ∘ a.2) = true) ↔ T a.1 (xs ∘ a.2) = false
    cases T a.1 (xs ∘ a.2) <;> simp
  · simp only [hp, reduceIte]
    change T a.1 (xs ∘ a.2) = true ↔ T a.1 (xs ∘ a.2) = true
    rfl

private theorem finite_inf_qf {L : FirstOrder.Language} {α β : Type*} [Finite β]
    (f : β → L.Formula α) (hf : ∀ b, (f b).IsQF) : (Formula.iInf f).IsQF := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  change (((Finset.univ : Finset β).toList.map f).foldr (fun a b => a ⊓ b) ⊤).IsQF
  generalize (Finset.univ : Finset β).toList = bs
  induction bs with
  | nil => exact BoundedFormula.IsQF.top
  | cons b bs ih => exact (hf b).inf ih

theorem profileFormula_qf {L : Signature} {k : ℕ} (p : Profile L k) :
    (profileFormula p).IsQF := by
  classical
  apply finite_inf_qf
  intro a
  split
  · exact Relations.isQF _ _
  · exact (Relations.isQF _ _).not

/-- The explicit ambient 0-type is retained even on the empty induced model. -/
def nullaryType {L : Signature} {V : Type v} (T : BoolTable L V) : Profile L 0 :=
  profile T Fin.elim0

@[simp] theorem nullaryType_pullback {L : Signature} {V : Type v} {W : Type w}
    (T : BoolTable L V) (f : W → V) :
    nullaryType (pullback T f) = nullaryType T := by
  funext a
  apply congrArg (T a.1)
  funext j
  exact Fin.elim0 (a.2 j)

end CCO.FullPhaseLift.Canonical
