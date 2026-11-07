import CCO.PairHomogeneity
import CCO.APRamseyReadout.OwnerAction
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Option

/-! Actual finite quantifier-free unions of the original complete
one/two-point types. Logical equality is included as its true diagonal.
The generic syntax leaf uses only original homogeneity; source-specific
owner imaginary codes must discharge invariance with their genuine action. -/

universe u v w r
namespace CCO.APRamseyReadout
open CCO
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Quantifier-free syntax in the retained original atoms and equality.
The declared input sorts retain the genuine unary sort labels. -/
inductive OldPairFormula (i j : ι) : Type w
  | truth
  | diagonal
  | atom (a : S.Atom i j)
  | neg (p : OldPairFormula i j)
  | conj (p q : OldPairFormula i j)
  | disj (p q : OldPairFormula i j)

namespace OldPairFormula
variable {S} {i j : ι}

def eval (x : X i) (y : X j) : OldPairFormula S i j → Prop
  | .truth => True
  | .diagonal => (⟨i,x⟩ : Sigma X) = ⟨j,y⟩
  | .atom a => S.atomRel a x y
  | .neg p => ¬ p.eval x y
  | .conj p q => p.eval x y ∧ q.eval x y
  | .disj p q => p.eval x y ∨ q.eval x y

def typeFormula (a : Option (S.Atom i j)) : OldPairFormula S i j :=
  match a with | none => .diagonal | some a => .atom a

theorem eval_typeFormula (a : Option (S.Atom i j)) (x : X i) (y : X j) :
    (typeFormula a).eval x y ↔ S.colour x y = a := by
  cases a with
  | none => exact (S.colour_none_iff x y).symm
  | some a => exact Iff.rfl

def disjoin : List (OldPairFormula S i j) → OldPairFormula S i j
  | [] => .neg .truth
  | p :: ps => .disj p (disjoin ps)

theorem eval_disjoin (ps : List (OldPairFormula S i j)) (x : X i) (y : X j) :
    (disjoin ps).eval x y ↔ ∃ p ∈ ps, p.eval x y := by
  induction ps with
  | nil => simp [disjoin,eval]
  | cons p ps ih => simp [disjoin,eval,ih]

/-- ALL syntax is preserved by full original types, including none. -/
theorem eval_colour_iff (p : OldPairFormula S i j) (x x' : X i) (y y' : X j)
    (h : S.colour x y = S.colour x' y') : p.eval x y ↔ p.eval x' y' := by
  induction p with
  | truth => exact Iff.rfl
  | diagonal =>
    exact (S.colour_none_iff x y).symm.trans
      ((Iff.of_eq (congrArg (fun a => a = none) h)).trans (S.colour_none_iff x' y'))
  | atom a => exact Iff.of_eq (congrArg (fun o => o = some a) h)
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

end OldPairFormula

/-- A finite genuine syntactic disjunction, rather than a mere assertion
that an unspecified definition is invariant under embeddings. -/
def nonOrderPairDefinition {i j : ι} (R : X i → X j → Prop) : OldPairFormula S i j := by
  classical
  letI := S.finiteAtom i j
  let types : Finset (Option (S.Atom i j)) := Finset.univ.filter
    (fun a => ∃ x y, S.colour x y = a ∧ R x y)
  exact OldPairFormula.disjoin (types.toList.map OldPairFormula.typeFormula)

theorem nonOrderPairDefinition_eval {i j : ι} (R : X i → X j → Prop) (x : X i) (y : X j) :
    (nonOrderPairDefinition S R).eval x y ↔
      ∃ x' y', S.colour x y = S.colour x' y' ∧ R x' y' := by
  classical
  letI := S.finiteAtom i j
  rw [nonOrderPairDefinition,OldPairFormula.eval_disjoin]
  constructor
  · rintro ⟨p,hp,hptrue⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    obtain ⟨_,x',y',hc,hr⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp ha)
    exact ⟨x',y',((OldPairFormula.eval_typeFormula a x y).mp hptrue).trans hc.symm,hr⟩
  · rintro ⟨x',y',hc,hr⟩
    refine ⟨OldPairFormula.typeFormula (S.colour x y),List.mem_map.mpr ⟨S.colour x y,?_,rfl⟩,?_⟩
    · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x',y',hc.symm,hr⟩)
    · exact (OldPairFormula.eval_typeFormula _ x y).mpr rfl

/-- Homogeneous complete atomic types yield the actual finite qf
union. Invariance is later proved for every particular owner term code. -/
theorem invariant_nonOrderPairDefinition
    {G : Type r} [Group G] [∀ i, MulAction G (X i)] (H : HomogeneousSource S G)
    {i j : ι} (R : X i → X j → Prop)
    (invariant : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y) (x : X i) (y : X j) :
    (nonOrderPairDefinition S R).eval x y ↔ R x y := by
  rw [nonOrderPairDefinition_eval]
  constructor
  · rintro ⟨x',y',hc,hr⟩
    obtain ⟨g,hx,hy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
    exact (invariant g x y).mp (by simpa only [hx,hy] using hr)
  · intro hr
    exact ⟨x,y,rfl,hr⟩


namespace OwnerNonOrderCode
open CCO.CloneTupleGeometry CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.TerminalPowers
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

abbrev Coordinate (i : B.Sorts) := OriginalNamedHiddenCoordinate (cloneSource B) (HF B) i

def termValue {i : B.Sorts} (D : Coordinate B i) {s : (Lang B ht).Sorts}
    (q : Term (Lang B ht) ⟨⟨i,Sum.inr D⟩⟩ s) (x : B.Point i) : Values B :=
  (Hidden B ht).eval q (originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
    (Quotient.mk D.val.val (x,0)))

theorem termValue_equivariant (g : CCO.TerminalPowers.FullAut B.source)
    {i : B.Sorts} (D : Coordinate B i) {s : (Lang B ht).Sorts}
    (q : Term (Lang B ht) ⟨⟨i,Sum.inr D⟩⟩ s) (x : B.Point i) :
    ownerHiddenHom B ht g • termValue B ht D q x = termValue B ht D q (g • x) :=
  ownerHidden_named_term B ht g D q x 0

variable {i j : B.Sorts} (D : Coordinate B i) (E : Coordinate B j)
variable {s t : (Lang B ht).Sorts}
variable (q : Term (Lang B ht) ⟨⟨i,Sum.inr D⟩⟩ s)
variable (p : Term (Lang B ht) ⟨⟨j,Sum.inr E⟩⟩ t)

def equalityCode (x : B.Point i) (y : B.Point j) : Prop :=
  termValue B ht D q x = termValue B ht E p y

theorem equalityCode_invariant (g : CCO.TerminalPowers.FullAut B.source) (x : B.Point i) (y : B.Point j) :
    equalityCode B ht D E q p (g • x) (g • y) ↔ equalityCode B ht D E q p x y := by
  unfold equalityCode
  rw [← termValue_equivariant B ht g D q x,← termValue_equivariant B ht g E p y]
  exact (MulAction.injective (ownerHiddenHom B ht g)).eq_iff

def functionCode (F : (Lang B ht).Func) (x : B.Point i) (y : B.Point j) : Prop :=
  (Hidden B ht).sort (termValue B ht D q x) = (Lang B ht).input F ∧
    (Hidden B ht).func F (termValue B ht D q x) = termValue B ht E p y

theorem functionCode_invariant (F : (Lang B ht).Func)
    (g : CCO.TerminalPowers.FullAut B.source) (x : B.Point i) (y : B.Point j) :
    functionCode B ht D E q p F (g • x) (g • y) ↔ functionCode B ht D E q p F x y := by
  unfold functionCode
  rw [← termValue_equivariant B ht g D q x,← termValue_equivariant B ht g E p y,
    (Hidden B ht).aut_sort,← ownerHidden_func]
  exact and_congr_right (fun _ => (MulAction.injective (ownerHiddenHom B ht g)).eq_iff)

def binaryCode (R : (Lang B ht).Rel) (x : B.Point i) (y : B.Point j) : Prop :=
  (Hidden B ht).rel R (fun n => if n.val = 0 then termValue B ht D q x else termValue B ht E p y)

theorem binaryCode_invariant (R : (Lang B ht).Rel)
    (g : CCO.TerminalPowers.FullAut B.source) (x : B.Point i) (y : B.Point j) :
    binaryCode B ht D E q p R (g • x) (g • y) ↔ binaryCode B ht D E q p R x y := by
  have he : (fun n : Fin ((Lang B ht).arity R) =>
      if n.val = 0 then termValue B ht D q (g • x) else termValue B ht E p (g • y)) =
      (fun z => ownerHiddenHom B ht g • z) ∘
        (fun n => if n.val = 0 then termValue B ht D q x else termValue B ht E p y) := by
    funext n
    by_cases hn : n.val = 0 <;>
      simp only [Function.comp_apply,hn,ite_true,ite_false,termValue_equivariant]
  unfold binaryCode
  rw [he]
  exact ownerHidden_rel B ht g R _

/-- Concrete finite qf definitions for EVERY actual named-coordinate
term code. Instantiating selected chart coordinates needs no new action
or arity-one owner interpretation, and no diagonal restriction. -/
theorem equality_qf (x : B.Point i) (y : B.Point j) :
    (nonOrderPairDefinition B.source (equalityCode B ht D E q p)).eval x y ↔
      equalityCode B ht D E q p x y :=
  invariant_nonOrderPairDefinition B.source B.homogeneous _ (equalityCode_invariant B ht D E q p) x y

theorem function_qf (F : (Lang B ht).Func) (x : B.Point i) (y : B.Point j) :
    (nonOrderPairDefinition B.source (functionCode B ht D E q p F)).eval x y ↔
      functionCode B ht D E q p F x y :=
  invariant_nonOrderPairDefinition B.source B.homogeneous _ (functionCode_invariant B ht D E q p F) x y

theorem binary_qf (R : (Lang B ht).Rel) (x : B.Point i) (y : B.Point j) :
    (nonOrderPairDefinition B.source (binaryCode B ht D E q p R)).eval x y ↔
      binaryCode B ht D E q p R x y :=
  invariant_nonOrderPairDefinition B.source B.homogeneous _ (binaryCode_invariant B ht D E q p R) x y

end OwnerNonOrderCode

end
end CCO.APRamseyReadout
