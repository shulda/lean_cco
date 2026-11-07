import CCO.UnfilteredEP.QuotientTermKernel
import CCO.UnfilteredEP.QuotientPairClosure
import CCO.UnfilteredEP.HierarchyBijectiveTerms
import CCO.UnfilteredEP.ResetEdgeSupportIso

/-!
# C37-C42 with only the explicit synchronized-context laws

The orders here are arbitrary supplied total orders. The two source
context laws are fixed hidden-SORT priority and synchronized named-path
comparisons INSIDE true parent fibres. No hierarchical normalizer theorem,
reset-square theorem, Ramsey arrow or EP provider proves this result.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1500000
universe u v w z z'
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryFreshFrames
open CCO.ParityHasse.Original CCO.TerminalLattice
noncomputable section

/-- The explicit A04 order context. These are comparison laws on the
actual existing named maps, with no pair-type, normalization or EP field. -/
structure SynchronizedPairOrder (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
    {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
    (hC : ActualAge B ht C) (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V) : Prop where
  path_parent : ∀ {D E : HiddenCut B} (p : NamedCutPath B ht D E)
    (x y : HiddenCutCarrier B ht C D),
    (actualCutSystem B ht C hC).parent D x y →
      (@LT.lt _ o.toLT (finitePathEquiv B ht C hC p x).val (finitePathEquiv B ht C hC p y).val ↔
        @LT.lt _ o.toLT x.val y.val)
  different_sort : ∀ x y : V, C.sort x ≠ C.sort y →
    (@LT.lt _ o.toLT x y ↔ @LT.lt _ priority.toLT (C.sort x) (C.sort y))

namespace SynchronizedPairType
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

private def properCut (s : (Sig B ht).Sorts) (hs : ProperSort B ht s) : HiddenCut B := by
  rcases s with ⟨⟨i,c⟩⟩
  cases c with
  | inl c => exact hs.elim
  | inr D => exact ⟨i,D⟩

private theorem properCut_sort (s : (Sig B ht).Sorts) (hs : ProperSort B ht s) :
    hiddenCutSort B ht (properCut B ht s hs) = s := by
  rcases s with ⟨⟨i,c⟩⟩
  cases c with
  | inl c => exact hs.elim
  | inr D => rfl
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

/-- The actual named inverse theorem turns any bijective term into a
path to which the explicit source synchronization law applies. -/
theorem bijective_term_parent
    (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V)
    (sync : SynchronizedPairOrder B ht C hC priority o)
    (e : C.Embedding (Target B ht)) (D E : HiddenCut B)
    (term : Term (Lang B ht) (hiddenCutSort B ht D) (hiddenCutSort B ht E))
    (bijective : Function.Bijective ((Hidden B ht).typedEval term))
    (x y : HiddenCutCarrier B ht C D)
    (hp : (actualCutSystem B ht C hC).parent D x y)
    (z v : V)
    (hz : e.point z = (Hidden B ht).eval term (e.point x.val))
    (hv : e.point v = (Hidden B ht).eval term (e.point y.val)) :
    @LT.lt _ o.toLT z v ↔ @LT.lt _ o.toLT x.val y.val := by
  obtain ⟨p,rfl⟩ := namedCutPath_of_bijective_term B ht D E term bijective
  have hz' : z = (finitePathEquiv B ht C hC p x).val :=
    e.injective (hz.trans (finitePathValue_ambient_eval B ht C hC e p x).symm)
  have hv' : v = (finitePathEquiv B ht C hC p y).val :=
    e.injective (hv.trans (finitePathValue_ambient_eval B ht C hC e p y).symm)
  rw [hz',hv']
  exact sync.path_parent p x y hp

/-- All four comparisons of two ordered marked endpoints depend only
on their two marks. -/
theorem ordered_pairMark_iff {V : Type z} {W : Type z'}
    (oV : LinearOrder V) (oW : LinearOrder W) (x y : V) (x' y' : W)
    (hxy : @LT.lt _ oV.toLT x y) (hxy' : @LT.lt _ oW.toLT x' y') (a b : Bool) :
    @LT.lt _ oW.toLT (pairMark x' y' a) (pairMark x' y' b) ↔
      @LT.lt _ oV.toLT (pairMark x y a) (pairMark x y b) := by
  cases a <;> cases b <;> simp only [pairMark]
  · exact iff_of_false (@lt_irrefl _ oW.toPreorder x') (@lt_irrefl _ oV.toPreorder x)
  · exact iff_of_true hxy' hxy
  · exact iff_of_false (@lt_asymm _ oW.toPreorder _ _ hxy') (@lt_asymm _ oV.toPreorder _ _ hxy)
  · exact iff_of_false (@lt_irrefl _ oW.toPreorder y') (@lt_irrefl _ oV.toPreorder y)

theorem named_parent_upper_of_key (D : HiddenCut B) (q t : HiddenCutPoint B D)
    (h : Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le q =
      Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le t) :
    originalUpperSetoid (cloneSource B) D.2.val
      (fullMIParent B (fullMIOfNamed B D.1 D.2))
      (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le q t := by
  induction q using Quotient.inductionOn with | _ x =>
    induction t using Quotient.inductionOn with | _ y =>
      exact (originalUpperSetoid_mk (cloneSource B) D.2.val
        (fullMIParent B (fullMIOfNamed B D.1 D.2))
        (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le x y).mpr (Quotient.exact h)

variable {V : Type z} {W : Type z'}
variable (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (D : CCO.UnarySupport.Structure (Sig B ht) W)
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D)
variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (priority : LinearOrder (Sig B ht).Sorts) (oC : LinearOrder V) (oD : LinearOrder W)

include properC in
/-- Comparison theorem for the canonical pointed motion, in arbitrary
actual finite members. Membership is in the WHOLE ambient pair closure;
no enumeration of displayed coordinates is used. -/
theorem pair_motion_order_iff
    (syncC : SynchronizedPairOrder B ht C hC priority oC)
    (syncD : SynchronizedPairOrder B ht D hD priority oD)
    (eC : C.Embedding (Target B ht)) (eD : D.Embedding (Target B ht))
    (J : HiddenCut B) (x y : HiddenCutCarrier B ht C J)
    (x' y' : HiddenCutCarrier B ht D J)
    (hp : (actualCutSystem B ht C hC).parent J x y)
    (hp' : (actualCutSystem B ht D hD).parent J x' y')
    (hxy : @LT.lt _ oC.toLT x.val y.val)
    (hxy' : @LT.lt _ oD.toLT x'.val y'.val)
    (g : (Hidden B ht).Aut)
    (hx : g • eC.point x.val = eD.point x'.val)
    (hy : g • eC.point y.val = eD.point y'.val)
    (z v : V) (z' v' : W)
    (hz : eD.point z' = g • eC.point z) (hv : eD.point v' = g • eC.point v)
    (hzmem : eC.point z ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val})
    (hvmem : eC.point v ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val}) :
    @LT.lt _ oD.toLT z' v' ↔
      @LT.lt _ oC.toLT z v := by
  have hsort (a : V) (a' : W) (ha : eD.point a' = g • eC.point a) : D.sort a' = C.sort a :=
    (eD.sort_eq a').symm.trans ((congrArg (Hidden B ht).sort ha).trans
      (((Hidden B ht).aut_sort g _).trans (eC.sort_eq a)))
  have hsz := hsort z z' hz
  have hsv := hsort v v' hv
  by_cases hs : C.sort z = C.sort v
  · obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C eC J x
    obtain ⟨t,ht'⟩ := finite_cut_point_realized B ht C eC J y
    have hsAmbient : (Hidden B ht).sort (eC.point z) = (Hidden B ht).sort (eC.point v) :=
      (eC.sort_eq z).trans (hs.trans (eC.sort_eq v).symm)
    rw [hq,ht'] at hzmem hvmem
    obtain ⟨a,b,term,htermz,htermv⟩ :=
      quotient_pair_common_term B ht J q t (eC.point z) (eC.point v) hsAmbient hzmem hvmem
    let E := properCut B ht (C.sort z) (properC z)
    have hE : (Hidden B ht).sort (eC.point z) = hiddenCutSort B ht E :=
      (eC.sort_eq z).trans (properCut_sort B ht (C.sort z) (properC z)).symm
    let term' : Term (Lang B ht) (hiddenCutSort B ht J) (hiddenCutSort B ht E) := hE ▸ term
    have htermz' : (Hidden B ht).eval term' (namedNode B J.2 (pairMark q t a)) = eC.point z :=
      (fresh_eval_cast_output B ht hE term _).trans htermz
    have htermv' : (Hidden B ht).eval term' (namedNode B J.2 (pairMark q t b)) = eC.point v :=
      (fresh_eval_cast_output B ht hE term _).trans htermv
    have hmarks (c : Bool) : eC.point (pairMark x y c).val = namedNode B J.2 (pairMark q t c) := by
      cases c
      · exact hq
      · exact ht'
    have hgmarks (c : Bool) : g • eC.point (pairMark x y c).val = eD.point (pairMark x' y' c).val := by
      cases c
      · exact hx
      · exact hy
    have hzC : eC.point z = (Hidden B ht).eval term' (eC.point (pairMark x y a).val) := by
      rw [hmarks]
      exact htermz'.symm
    have hvC : eC.point v = (Hidden B ht).eval term' (eC.point (pairMark x y b).val) := by
      rw [hmarks]
      exact htermv'.symm
    have hzD : eD.point z' = (Hidden B ht).eval term' (eD.point (pairMark x' y' a).val) := by
      rw [hz,hzC,(Hidden B ht).aut_eval,hgmarks]
    have hvD : eD.point v' = (Hidden B ht).eval term' (eD.point (pairMark x' y' b).val) := by
      rw [hv,hvC,(Hidden B ht).aut_eval,hgmarks]
    rcases actual_terminal_quotient_term_split B ht (fullMIOfNamed B J.1 J.2) term' with bij | collapse
    · have hpab : (actualCutSystem B ht C hC).parent J (pairMark x y a) (pairMark x y b) := by
        cases a <;> cases b
        · exact (actualCutSystem B ht C hC).parent_refl _ _
        · exact hp
        · exact (actualCutSystem B ht C hC).parent_symm _ hp
        · exact (actualCutSystem B ht C hC).parent_refl _ _
      have hpab' : (actualCutSystem B ht D hD).parent J (pairMark x' y' a) (pairMark x' y' b) := by
        cases a <;> cases b
        · exact (actualCutSystem B ht D hD).parent_refl _ _
        · exact hp'
        · exact (actualCutSystem B ht D hD).parent_symm _ hp'
        · exact (actualCutSystem B ht D hD).parent_refl _ _
      have hCterm := bijective_term_parent B ht C hC priority oC syncC eC
        J E term' bij (pairMark x y a) (pairMark x y b) hpab z v hzC hvC
      have hDterm := bijective_term_parent B ht D hD priority oD syncD eD
        J E term' bij (pairMark x' y' a) (pairMark x' y' b) hpab' z' v' hzD hvD
      simp only [pairMark_subtype_val] at hCterm hDterm
      exact hDterm.trans ((ordered_pairMark_iff
        oC
        oD
        x.val y.val x'.val y'.val hxy hxy' a b).trans hCterm.symm)
    · let parent := originalUpperSetoid (cloneSource B) J.2.val
        (fullMIParent B (fullMIOfNamed B J.1 J.2))
        (fullMIParent_cover B (fullMIOfNamed B J.1 J.2)).le
      have hparent := named_parent_upper_of_key B J q t
        ((actualCutSystem_parent_realization B ht C hC eC J x y q t hq ht').mp hp)
      have hpab : originalUpperSetoid (cloneSource B) J.2.val
          (fullMIParent B (fullMIOfNamed B J.1 J.2))
          (fullMIParent_cover B (fullMIOfNamed B J.1 J.2)).le
          (pairMark q t a) (pairMark q t b) := by
        cases a <;> cases b
        · exact parent.refl _
        · exact hparent
        · exact parent.symm hparent
        · exact parent.refl _
      have he : z = v := eC.injective
        (htermz'.symm.trans ((collapse _ _ hpab).trans htermv'))
      have he' : z' = v' := eD.injective (hz.trans ((congrArg (fun p => g • eC.point p) he).trans hv.symm))
      rw [he,he']
      exact iff_of_false (@lt_irrefl _ oD.toPreorder _)
        (@lt_irrefl _ oC.toPreorder _)
  · have hs' : D.sort z' ≠ D.sort v' := fun h => hs (hsz.symm.trans (h.trans hsv))
    exact (syncD.different_sort z' v' hs').trans
      ((by rw [hsz,hsv] : @LT.lt _ priority.toLT (D.sort z') (D.sort v') ↔
        @LT.lt _ priority.toLT (C.sort z) (C.sort v)).trans
          (syncC.different_sort z v hs).symm)


open CCO.TerminalPowers CCO.UnaryTermsReturn

/-- A hidden automorphism is an isomorphism of its whole faithful
partial interpretation, preserving every old cylinder and function graph. -/
def hiddenPartialMotion (g : (Hidden B ht).Aut) :
    (Target B ht).DiagramIso (Target B ht) where
  equiv := g.val
  sort_eq x := (Hidden B ht).aut_sort g x
  func_iff F x y := by
    classical
    change ((g • y) ∈ if (Hidden B ht).sort (g • x) = (Lang B ht).input F then
      {(Hidden B ht).func F (g • x)} else ∅) ↔
      (y ∈ if (Hidden B ht).sort x = (Lang B ht).input F then
        {(Hidden B ht).func F x} else ∅)
    rw [(Hidden B ht).aut_sort g x]
    by_cases hs : (Hidden B ht).sort x = (Lang B ht).input F
    · simp only [hs,ite_true,Set.mem_singleton_iff]
      rw [← (Hidden B ht).aut_func g F x]
      exact g.val.injective.eq_iff
    · simp only [hs,ite_false,Set.mem_empty_iff_false]
  rel_iff R xs := (Hidden B ht).aut_rel g R xs

/-- Completeness of an arbitrary original quotient orbital gives one
original motion on both endpoints. There is no reset-square hypothesis. -/
theorem complete_orbital_hidden_motion {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (first second : CloneSAP.Carrier B.Point i)
    (q t q' t' : Quotient J.val.val)
    (hqt : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.val first second q t)
    (hqt' : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.val first second q' t') :
    ∃ g : (Hidden B ht).Aut,
      g • coordinateNode B ht J q = coordinateNode B ht J q' ∧
      g • coordinateNode B ht J t = coordinateNode B ht J t' := by
  let : MulAction (FullAut (cloneSource B)) (Quotient J.val.val) :=
    originalQuotientAction (cloneSource B) (cloneHomogeneous B) J.val
  obtain ⟨g,hgq,hgt⟩ := hqt
  obtain ⟨h,hhq,hht⟩ := hqt'
  have hgq' : g • Quotient.mk J.val.val first = q := hgq
  have hgt' : g • Quotient.mk J.val.val second = t := hgt
  have hhq' : h • Quotient.mk J.val.val first = q' := hhq
  have hht' : h • Quotient.mk J.val.val second = t' := hht
  let k := h*g⁻¹
  have hq : k • q = q' := by
    change (h*g⁻¹) • q = q'
    rw [mul_smul,← hgq',inv_smul_smul]
    exact hhq'
  have ht' : k • t = t' := by
    change (h*g⁻¹) • t = t'
    rw [mul_smul,← hgt',inv_smul_smul]
    exact hht'
  let motion := CCO.TypedOrbitFrames.originalCompletedMotionHom (cloneSource B) (HF B)
    (cloneSAP B) (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) k
  have value (a : Quotient J.val.val) :
      motion • coordinateNode B ht J a = coordinateNode B ht J (k • a) := by
    induction a using Quotient.inductionOn with | _ x => rfl
  exact ⟨motion,(value q).trans (congrArg (coordinateNode B ht J) hq),
    (value t).trans (congrArg (coordinateNode B ht J) ht')⟩

include properC in
/-- Exact C37-C42 source export. The arbitrary complete external orbital
and the two explicit synchronized-order laws determine a WHOLE induced
pointed pair isomorphism. Every atomic relation, function domain/value,
equality and order comparison is preserved, with both marks retained. -/
theorem complete_relative_orbital_pointed_type
    (syncC : SynchronizedPairOrder B ht C hC priority oC)
    (syncD : SynchronizedPairOrder B ht D hD priority oD)
    (eC : C.Embedding (Target B ht)) (eD : D.Embedding (Target B ht))
    (J : HiddenCut B) (first second : CloneSAP.Carrier B.Point J.1)
    (parent : fullMIParent B (fullMIOfNamed B J.1 J.2) first second)
    (_external : ¬ J.2.val first second)
    (x y : HiddenCutCarrier B ht C J) (x' y' : HiddenCutCarrier B ht D J)
    (q t q' t' : HiddenCutPoint B J)
    (hxq : eC.point x.val = namedNode B J.2 q)
    (hyt : eC.point y.val = namedNode B J.2 t)
    (hxq' : eD.point x'.val = namedNode B J.2 q')
    (hyt' : eD.point y'.val = namedNode B J.2 t')
    (hqt : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.2.val first second q t)
    (hqt' : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.2.val first second q' t')
    (hxy : @LT.lt _ oC.toLT x.val y.val) (hxy' : @LT.lt _ oD.toLT x'.val y'.val) :
    ∃ g : (Hidden B ht).Aut,
      ∃ f : (C.closureStructure {x.val,y.val}).DiagramIso
        (D.closureStructure {x'.val,y'.val}),
      (∀ z, eD.point (f.equiv z).val = g • eC.point z.val) ∧
      (f.equiv ⟨x.val,C.subset_closure _ (by simp)⟩).val = x'.val ∧
      (f.equiv ⟨y.val,C.subset_closure _ (by simp)⟩).val = y'.val ∧
      ∀ z v, @LT.lt _ oD.toLT (f.equiv z).val (f.equiv v).val ↔ @LT.lt _ oC.toLT z.val v.val := by
  let fullJ := fullMIOfNamed B J.1 J.2
  obtain ⟨g,hgq,hgt⟩ := complete_orbital_hidden_motion B ht fullJ first second q t q' t' hqt hqt'
  have hx : g • eC.point x.val = eD.point x'.val :=
    (congrArg (fun a => g • a) hxq).trans (hgq.trans hxq'.symm)
  have hy : g • eC.point y.val = eD.point y'.val :=
    (congrArg (fun a => g • a) hyt).trans (hgt.trans hyt'.symm)
  have upper := originalQuotientOrbital_inside_originalUpper (cloneSource B) (cloneHomogeneous B)
    J.2.val (fullMIParent B fullJ) (fullMIParent_cover B fullJ).le first second parent
  have upper_eq (a b : HiddenCutPoint B J) :
      originalUpperSetoid (cloneSource B) J.2.val (fullMIParent B fullJ)
        (fullMIParent_cover B fullJ).le a b →
      Quot.mapRight (fullMIParent_cover B fullJ).le a =
        Quot.mapRight (fullMIParent_cover B fullJ).le b := by
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        intro hab
        exact Quotient.sound ((originalUpperSetoid_mk (cloneSource B) J.2.val
          (fullMIParent B fullJ) (fullMIParent_cover B fullJ).le a b).mp hab)
  have hp : (actualCutSystem B ht C hC).parent J x y :=
    (actualCutSystem_parent_realization B ht C hC eC J x y q t hxq hyt).mpr
      (upper_eq q t (upper q t hqt))
  have hp' : (actualCutSystem B ht D hD).parent J x' y' :=
    (actualCutSystem_parent_realization B ht D hD eD J x' y' q' t' hxq' hyt').mpr
      (upper_eq q' t' (upper q' t' hqt'))
  obtain ⟨f,hf,hfx,hfy⟩ := realized_support_pair_iso eC eD (hiddenPartialMotion B ht g)
    x.val y.val x'.val y'.val hx hy
  have ambient_mem (z : C.closure {x.val,y.val}) :
      eC.point z.val ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val} := by
    have hz : eC.point z.val ∈ eC.point '' C.closure {x.val,y.val} := ⟨z.val,z.property,rfl⟩
    rw [support_embedding_closure_image eC] at hz
    simp only [Set.image_insert_eq,Set.image_singleton] at hz
    exact actual_partial_closure_eq (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) _ ▸ hz
  refine ⟨g,f,hf,hfx,hfy,?_⟩
  intro z v
  exact pair_motion_order_iff B ht C D hC hD properC priority oC oD syncC syncD eC eD J
    x y x' y' hp hp' hxy hxy' g hx hy z.val v.val (f.equiv z).val (f.equiv v).val
    (hf z) (hf v) (ambient_mem z) (ambient_mem v)

end SynchronizedPairType
end
end CCO.UnfilteredEP
