import CCO.UnfilteredEP.ParentFormula
import CCO.UnfilteredEP.ResetCylinder

/-! Literal reset predicates augment the existing parent-key formula.
The original cylinder name is retained, and no function symbol changes. -/

universe u v w a
namespace CCO.UnfilteredEP
noncomputable section
open CCO.FullCode

structure CutFormula (L : Language.{a}) extends ParentFormula L where
  resetName : L.Binary
  resetLeft : L.leftSort resetName = sourceSort
  resetRight : L.rightSort resetName = sourceSort

namespace CutFormula
variable {L : Language.{a}} (F : CutFormula L)

abbrev same {V : Type v} (C : Structure L V) := F.toParentFormula.same C

def reset {V : Type v} (C : Structure L V) (x y : V) : Prop := C.binary F.resetName x y

theorem reset_natural {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (e : Structure.Embedding C D) (x y : V) :
    F.reset D (e.point x) (e.point y) ↔ F.reset C x y := e.binary_iff _ _ _

theorem reset_sorted {V : Type v} (C : Structure L V) {x y : V} (h : F.reset C x y) :
    C.sort x = F.sourceSort ∧ C.sort y = F.sourceSort := by
  obtain ⟨hx,hy⟩ := C.binary_sorted F.resetName x y h
  exact ⟨hx.trans F.resetLeft,hy.trans F.resetRight⟩

end CutFormula

open CCO.APRamseyReadout CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

def actualCutFormula (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2)) :
    CutFormula (CoordinateLanguage B ht) where
  __ := actualParentFormula B ht D
  resetName := resetCylinderName B ht (fullMIOfNamed B D.1 D.2) m
  resetLeft := rfl
  resetRight := rfl

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe z
variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C) (e : C.Embedding (Target B ht))

theorem actualCutFormula_reset_realization (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
    (x y : HiddenCutCarrier B ht C D)
    (q t : Quotient D.2.val.val)
    (hq : e.point x.val = namedNode B D.2 q) (ht' : e.point y.val = namedNode B D.2 t) :
    (actualCutFormula B ht D m).reset (CoordinateModel B ht C) x.val y.val ↔
      m.relation q t := by
  let J := fullMIOfNamed B D.1 D.2
  have he := (CCO.TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) e).binary_iff (resetCylinderName B ht J m) x.val y.val
  change (CoordinateTarget B ht).binary (resetCylinderName B ht J m)
    (e.point x.val) (e.point y.val) ↔ _ at he
  rw [hq,ht'] at he
  exact he.symm.trans (resetCylinderName_iff B ht J m q t)

include e

theorem actualCutFormula_reset_symmetric (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2)) (x y : V)
    (h : (actualCutFormula B ht D m).reset (CoordinateModel B ht C) x y) :
    (actualCutFormula B ht D m).reset (CoordinateModel B ht C) y x := by
  obtain ⟨hx,hy⟩ := (actualCutFormula B ht D m).reset_sorted (CoordinateModel B ht C) h
  let xd : HiddenCutCarrier B ht C D := ⟨x,hx⟩
  let yd : HiddenCutCarrier B ht C D := ⟨y,hy⟩
  obtain ⟨q,hq⟩ := CCO.TypedOrbitFrames.original_completed_hidden_carrier_exists
    (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point x,(e.sort_eq x).trans hx⟩
  obtain ⟨t,ht'⟩ := CCO.TypedOrbitFrames.original_completed_hidden_carrier_exists
    (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point y,(e.sort_eq y).trans hy⟩
  exact (actualCutFormula_reset_realization B ht C e D m yd xd t q ht' hq).mpr
    (m.symmetric ((actualCutFormula_reset_realization B ht C e D m xd yd q t hq ht').mp h))

theorem actualCutFormula_reset_ne (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2)) (x y : V)
    (h : (actualCutFormula B ht D m).reset (CoordinateModel B ht C) x y) : x ≠ y := by
  intro he
  subst y
  have hs := (actualCutFormula B ht D m).reset_sorted (CoordinateModel B ht C) h
  let xd : HiddenCutCarrier B ht C D := ⟨x,hs.1⟩
  obtain ⟨q,hq⟩ := CCO.TypedOrbitFrames.original_completed_hidden_carrier_exists
    (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point x,(e.sort_eq x).trans hs.1⟩
  exact m.irreflexive q ((actualCutFormula_reset_realization B ht C e D m xd xd q q hq hq).mp h)

include hC

theorem actualCutFormula_reset_same (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2)) (x y : V)
    (h : (actualCutFormula B ht D m).reset (CoordinateModel B ht C) x y) :
    (actualParentFormula B ht D).same (CoordinateModel B ht C) x y := by
  obtain ⟨hx,hy⟩ := (actualCutFormula B ht D m).reset_sorted (CoordinateModel B ht C) h
  let xd : HiddenCutCarrier B ht C D := ⟨x,hx⟩
  let yd : HiddenCutCarrier B ht C D := ⟨y,hy⟩
  obtain ⟨q,hq⟩ := CCO.TypedOrbitFrames.original_completed_hidden_carrier_exists
    (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point x,(e.sort_eq x).trans hx⟩
  obtain ⟨t,ht'⟩ := CCO.TypedOrbitFrames.original_completed_hidden_carrier_exists
    (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point y,(e.sort_eq y).trans hy⟩
  have hReset := (actualCutFormula_reset_realization B ht C e D m xd yd q t hq ht').mp h
  have hParent := m.inside_parent hReset
  apply (actualParentFormula_same_iff B ht C hC D xd yd).mpr
  exact (actualCutSystem_parent_realization B ht C hC e D xd yd q t hq ht').mpr hParent

end
end CCO.UnfilteredEP
