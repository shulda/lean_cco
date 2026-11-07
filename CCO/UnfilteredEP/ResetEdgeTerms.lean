import CCO.UnfilteredEP.QuotientTermKernel
import CCO.UnfilteredEP.HierarchyBijectiveTerms
import CCO.UnfilteredEP.HierarchyComparisons

/-! Every point of a whole proper quotient-pair closure is a term value
of one marked endpoint. Terminal holonomy makes the term in a fixed
named target independent of that choice of endpoint. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryFreshFrames
open CCO.ParityHasse.Original
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- A two-mark selector keeps the same orientation in every realization. -/
def pairMark {V : Type z} (x y : V) : Bool → V
  | false => x
  | true => y

@[simp] theorem pairMark_false {V : Type z} (x y : V) : pairMark x y false = x := rfl
@[simp] theorem pairMark_true {V : Type z} (x y : V) : pairMark x y true = y := rfl

@[simp] theorem pairMark_subtype_val {V : Type z} {P : V → Prop}
    (x y : {x // P x}) (a : Bool) : (pairMark x y a).val = pairMark x.val y.val a := by
  cases a <;> rfl

theorem fresh_eval_cast_output {s t t' : (Lang B ht).Sorts} (h : t = t')
    (term : Term (Lang B ht) s t) (x : Values B) :
    (Hidden B ht).eval (h ▸ term) x = (Hidden B ht).eval term x := by
  cases h
  rfl

/-- Membership ranges over the entire actual unary closure. -/
theorem quotient_pair_point_term (D : HiddenCut B) (q t : HiddenCutPoint B D)
    (z : Values B)
    (hz : z ∈ (Hidden B ht).closure {namedNode B D.2 q,namedNode B D.2 t}) :
    ∃ a : Bool, ∃ term : Term (Lang B ht) (hiddenCutSort B ht D) ((Hidden B ht).sort z),
      (Hidden B ht).eval term (namedNode B D.2 (pairMark q t a)) = z := by
  obtain ⟨p,hp,s,term,hterm⟩ := hz
  rcases Set.mem_insert_iff.mp hp with hp | hp
  · subst p
    have hs : s = (Hidden B ht).sort z :=
      ((Hidden B ht).eval_sort term rfl).symm.trans (congrArg (Hidden B ht).sort hterm)
    subst s
    exact ⟨false,term,hterm⟩
  · have hp' : p = namedNode B D.2 t := hp
    subst p
    have hs : s = (Hidden B ht).sort z :=
      ((Hidden B ht).eval_sort term rfl).symm.trans (congrArg (Hidden B ht).sort hterm)
    subst s
    exact ⟨true,term,hterm⟩

/-- In a fixed named target one common actual term evaluates both
points, even when they were generated through different mixed paths. -/
theorem quotient_pair_common_term (D : HiddenCut B) (q t : HiddenCutPoint B D)
    (z v : Values B) (hs : (Hidden B ht).sort z = (Hidden B ht).sort v)
    (hz : z ∈ (Hidden B ht).closure {namedNode B D.2 q,namedNode B D.2 t})
    (hv : v ∈ (Hidden B ht).closure {namedNode B D.2 q,namedNode B D.2 t}) :
    ∃ a b : Bool, ∃ term : Term (Lang B ht) (hiddenCutSort B ht D) ((Hidden B ht).sort z),
      (Hidden B ht).eval term (namedNode B D.2 (pairMark q t a)) = z ∧
      (Hidden B ht).eval term (namedNode B D.2 (pairMark q t b)) = v := by
  obtain ⟨a,left,hl⟩ := quotient_pair_point_term B ht D q t z hz
  obtain ⟨b,right,hr⟩ := quotient_pair_point_term B ht D q t v hv
  let right' : Term (Lang B ht) (hiddenCutSort B ht D) ((Hidden B ht).sort z) := hs.symm ▸ right
  have hr' : (Hidden B ht).eval right' (namedNode B D.2 (pairMark q t b)) = v :=
    (fresh_eval_cast_output B ht hs.symm right _).trans hr
  have h := congrArg Subtype.val (congrFun
    (actual_quotient_terms_eq (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (fun i E F hEF x => B.terminal_interval_infinite ht E F hEF x) D.2 left right')
    ⟨namedNode B D.2 (pairMark q t b),rfl⟩)
  exact ⟨a,b,left,hl,h.trans hr'⟩

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C)

theorem finitePathValue_ambient_eval (e : C.Embedding (Target B ht))
    {D E : HiddenCut B} (p : NamedCutPath B ht D E) (x : HiddenCutCarrier B ht C D) :
    e.point (finitePathValue B ht C hC p x).val =
      (Hidden B ht).eval p.forward (e.point x.val) := by
  have hm := e.toHom.map_eval (freshSupportTerm B ht p.forward)
    (C.value_mem (CCO.TerminalHiddenHN.actualAge_total _ _ _ _ hC) _ x)
  exact (freshSupportTerm_target_eval B ht p.forward _ _
    ((e.sort_eq x.val).trans x.property)).mp hm

/-- An arbitrary actual bijective term preserves normalized comparisons
inside the true parent fibre; its inverse was proved in the named syntax. -/
theorem hierarchicalOrder_bijective_term_parent
    (proper : ∀ x, ProperSort B ht (C.sort x))
    (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V)
    (e : C.Embedding (Target B ht)) (D E : HiddenCut B)
    (term : Term (Lang B ht) (hiddenCutSort B ht D) (hiddenCutSort B ht E))
    (bijective : Function.Bijective ((Hidden B ht).typedEval term))
    (x y : HiddenCutCarrier B ht C D)
    (hp : (actualCutSystem B ht C hC).parent D x y)
    (z v : V)
    (hz : e.point z = (Hidden B ht).eval term (e.point x.val))
    (hv : e.point v = (Hidden B ht).eval term (e.point y.val)) :
    @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT z v ↔
      @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT x.val y.val := by
  obtain ⟨p,rfl⟩ := namedCutPath_of_bijective_term B ht D E term bijective
  have hz' : z = (finitePathEquiv B ht C hC p x).val :=
    e.injective (hz.trans (finitePathValue_ambient_eval B ht C hC e p x).symm)
  have hv' : v = (finitePathEquiv B ht C hC p y).val :=
    e.injective (hv.trans (finitePathValue_ambient_eval B ht C hC e p y).symm)
  rw [hz',hv']
  exact hierarchicalOrder_path_parent B ht C proper hC priority o p x y hp

end
end CCO.UnfilteredEP
