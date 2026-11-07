import CCO.FullCode.Terms
import CCO.UnfilteredEP.HierarchyKeys

/-! Literal cut-fibre formulas. Their naturality holds on
ALL partial structures and ALL induced maps, rather than presupposing
age membership. Actual source totality is needed only to identify the
key formula with the named quotient parent. -/

universe u v w z a b
namespace CCO.UnfilteredEP
noncomputable section

section General
open CCO.FullCode

structure ParentFormula (L : Language.{a}) where
  sourceSort : L.Sorts
  keyCount : ℕ
  keySort : Fin keyCount → L.Sorts
  key : ∀ k, Term L sourceSort (keySort k)

namespace ParentFormula
variable {L : Language.{a}} (F : ParentFormula L)

def same {V : Type v} (C : Structure L V) (x y : V) : Prop :=
  C.sort x = F.sourceSort ∧ C.sort y = F.sourceSort ∧
    ∀ k, ∃ z, z ∈ (F.key k).eval C x ∧ z ∈ (F.key k).eval C y

theorem same_symm {V : Type v} (C : Structure L V) {x y : V} :
    F.same C x y → F.same C y x := by
  rintro ⟨hx,hy,h⟩
  exact ⟨hy,hx,fun k => by obtain ⟨z,hz,hz'⟩ := h k; exact ⟨z,hz',hz⟩⟩

theorem same_trans {V : Type v} (C : Structure L V) {x y z : V}
    (hxy : F.same C x y) (hyz : F.same C y z) : F.same C x z := by
  refine ⟨hxy.1,hyz.2.1,?_⟩
  intro k
  obtain ⟨a,hxa,hya⟩ := hxy.2.2 k
  obtain ⟨b,hyb,hzb⟩ := hyz.2.2 k
  have hab : a = b := (F.key k).functional C y hya hyb
  exact ⟨a,hxa,hab.symm ▸ hzb⟩

theorem same_natural {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (e : Structure.Embedding C D) (x y : V) :
    F.same D (e.point x) (e.point y) ↔ F.same C x y := by
  unfold same
  rw [e.sort_eq,e.sort_eq]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h k
    obtain ⟨z,hxz,hyz⟩ := h k
    obtain ⟨a,ha,he⟩ := ((F.key k).transport e x z).mp hxz
    subst z
    exact ⟨a,ha,((F.key k).map_iff e y a).mp hyz⟩
  · intro h k
    obtain ⟨z,hxz,hyz⟩ := h k
    exact ⟨e.point z,((F.key k).map_iff e x z).mpr hxz,
      ((F.key k).map_iff e y z).mpr hyz⟩

end ParentFormula
end General

section Actual
open CCO.APRamseyReadout CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- No coordinate is selected pointwise: every strict coarser proper
MI key is a fixed existing upward term, including an empty Top key. -/
def actualParentFormula (D : HiddenCut B) :
    ParentFormula (CoordinateLanguage B ht) where
  sourceSort := hiddenCutSort B ht D
  keyCount := coarserCutCount B D
  keySort k := hiddenCutSort B ht (hiddenKeyCut B D k)
  key k := CCO.TerminalHiddenHN.supportTermToFull (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (hiddenUpwardTerm B ht D.2 (coarserCutEnumeration B D k).val
      (coarserCutEnumeration B D k).property.le)

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C)

theorem actualParentFormula_value_mem (D : HiddenCut B)
    (k : Fin (coarserCutCount B D)) (x : HiddenCutCarrier B ht C D) :
    (hiddenUpwardValue B ht C hC D k x).val ∈
      ((actualParentFormula B ht D).key k).eval (CoordinateModel B ht C) x.val := by
  change (hiddenUpwardValue B ht C hC D k x).val ∈
    (CCO.TerminalHiddenHN.supportTermToFull (Sig B ht)
      (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
        (cloneSAP B) (fullCovers B ht))
      (hiddenUpwardTerm B ht D.2 (coarserCutEnumeration B D k).val
        (coarserCutEnumeration B D k).property.le)).eval (CoordinateModel B ht C) x.val
  rw [CCO.TerminalHiddenHN.supportTermToFull_eval]
  exact C.value_mem (CCO.TerminalHiddenHN.actualAge_total _ _ _ _ hC) _ x

/-- On each ACTUAL member the literal formula is the complete
named-parent key relation used by the proved hierarchy. -/
theorem actualParentFormula_same_iff (D : HiddenCut B)
    (x y : HiddenCutCarrier B ht C D) :
    (actualParentFormula B ht D).same (CoordinateModel B ht C) x.val y.val ↔
      (actualCutSystem B ht C hC).parent D x y := by
  constructor
  · intro h k
    obtain ⟨a,ha,hb⟩ := h.2.2 k
    have hx := actualParentFormula_value_mem B ht C hC D k x
    have hy := actualParentFormula_value_mem B ht C hC D k y
    apply Subtype.ext
    exact (((actualParentFormula B ht D).key k).functional
      (CoordinateModel B ht C) x.val hx ha).trans
        (((actualParentFormula B ht D).key k).functional
          (CoordinateModel B ht C) y.val hb hy)
  · intro h
    refine ⟨x.property,y.property,?_⟩
    intro k
    refine ⟨(hiddenUpwardValue B ht C hC D k x).val,
      actualParentFormula_value_mem B ht C hC D k x,?_⟩
    have he : (hiddenUpwardValue B ht C hC D k x).val =
        (hiddenUpwardValue B ht C hC D k y).val := congrArg Subtype.val (h k)
    exact he.symm ▸ actualParentFormula_value_mem B ht C hC D k y

end Actual
end
end CCO.UnfilteredEP
