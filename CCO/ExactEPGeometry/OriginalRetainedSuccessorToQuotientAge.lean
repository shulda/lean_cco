import CCO.ExactEPGeometry.OriginalRetainedComparisonTables
import CCO.ExactEPGeometry.OriginalRetainedActualSelectedMixedAgeIff
import CCO.ExactEPGeometry.OriginalRetainedSelectedCorrectedMarkLegal
import CCO.ExactEPGeometry.OriginalPhaseSelectedProjectionReadout
import CCO.FullPhaseLift.BinarySource.MarkedComparisonSupport
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# B062 C96/C103: the WHOLE actual selected successor age occurs in the quotient

An arbitrary actual selected-successor tuple projects injectively to its
true old selected source. Split its finite index set by actual reachability;
active vertices are represented on their true reached occupancy anchors,
and inactive vertices keep the prescribed zero bit. The already proved
two-way C96 theorem gives ONE real old successor chart with distinct global
original E-classes. Projecting that whole chart to the actual selected
quotient retains injection, actual child names and every common old colour.

No extra old-representative injection, quotient age/SAP, action section,
chosen seed homogeneity or future source instance is hypothesized.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry FullPhaseLift.BinarySource.MarkedComparison
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Every finite induced tuple of the actual retained selected phase
successor occurs in the ACTUAL next original-E selected quotient, with
the ENTIRE common name table, including both real child owners. -/
theorem originalRetainedSuccessorToQuotientAge :
    AgeMaps (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE)
      (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE) := by
  classical
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let M := SingleStep.successor QB φ
  let RM := SingleStep.projection QB φ
  let IM := SingleStep.identification QB φ
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  let πN := originalCurrentToSelectedPoint A N (P.compose R) hN base hBase E
  let πB := originalCurrentToSelectedPoint A B P transport base hBase E
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  intro n p
  let old : Fin n → Sigma QB.Point := fun i => RM.project (p i)
  let bits : Fin n → Bit := fun i => (p i).1.2.val
  have hOldInj : Function.Injective old := RM.bijective.1.comp p.injective
  have hMark := UnarySource.global_marking IM
  have hBit (i : Fin n) : UnarySource.mark IM (old i) = bits i :=
    congrArg Subtype.val (p i).2.property
  have hLegal : Age.Legal QB.source φ.masks old bits := by
    constructor
    · intro i
      have h := hMark.1 (old i)
      rw [hBit i] at h
      exact h
    · intro i j
      have h := hMark.2 (old i) (old j)
      rw [hBit i,hBit j] at h
      exact h
  let active : Fin n → Prop := fun i => Nonempty (Bridge QB.source KQ (old i).1)
  let Active := {i : Fin n // active i}
  let Inactive := {i : Fin n // ¬active i}
  letI : Fintype Active := Fintype.ofFinite Active
  letI : Fintype Inactive := Fintype.ofFinite Inactive
  let na := Fintype.card Active
  let ni := Fintype.card Inactive
  let a : Fin na ≃ Active := (Fintype.equivFin Active).symm
  let b : Fin ni ≃ Inactive := (Fintype.equivFin Inactive).symm
  let index : Sum (Fin na) (Fin ni) ≃ Fin n :=
    (Equiv.sumCongr a b).trans (Equiv.sumCompl active)
  let ia : Fin na → Fin n := fun i => (a i).val
  let ii : Fin ni → Fin n := fun j => (b j).val
  have hActive (i : Fin na) :
      ∃ (c : Occ) (x : QB.Point (Quotient.mk'' (anchor c).val)),
        (⟨Quotient.mk'' (anchor c).val,x⟩ : Sigma QB.Point) = old (ia i) :=
    originalRetainedSelectedActivePoint_on_anchor A B P transport tp hOne Kroot E hE
      (old (ia i)) (a i).property
  let owners (i : Fin na) : Occ := Classical.choose (hActive i)
  let points (i : Fin na) : QB.Point (Quotient.mk'' (anchor (owners i)).val) :=
    Classical.choose (Classical.choose_spec (hActive i))
  have hPoint (i : Fin na) :
      (⟨Quotient.mk'' (anchor (owners i)).val,points i⟩ : Sigma QB.Point) = old (ia i) :=
    Classical.choose_spec (Classical.choose_spec (hActive i))
  let inactivePoints : Fin ni → Sigma QB.Point := fun j => old (ii j)
  let activeBits : Fin na → Bit := fun i => bits (ia i)
  let mixed : Sum (Fin na) (Fin ni) → Sigma QB.Point := fun v =>
    match v with
    | Sum.inl i => ⟨Quotient.mk'' (anchor (owners i)).val,points i⟩
    | Sum.inr j => inactivePoints j
  let allBits : Sum (Fin na) (Fin ni) → Bit := fun v =>
    match v with | Sum.inl i => activeBits i | Sum.inr _ => 0
  have hMixed (v : Sum (Fin na) (Fin ni)) : mixed v = old (index v) := by
    cases v with
    | inl i => exact hPoint i
    | inr j => rfl
  have hAllBits (v : Sum (Fin na) (Fin ni)) : allBits v = bits (index v) := by
    cases v with
    | inl i => rfl
    | inr j =>
      exact ((p (ii j)).1.2.property (b j).property).symm
  have hMixedInj : Function.Injective mixed := by
    intro v w h
    apply index.injective
    apply hOldInj
    exact (hMixed v).symm.trans (h.trans (hMixed w))
  have hInactive (j : Fin ni) :
      ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative A B P transport base hBase E (inactivePoints j)).1) := by
    let q := inactivePoints j
    let rep := originalSelectedTaggedRepresentative A B P transport base hBase E q
    have hClass : (Quotient.mk'' rep.1 : QB.Sorts) = q.1 :=
      originalOccupancyRepresentative_class A B P base hBase E q.1
    intro hOld
    have hNew := (originalRetainedSelectedReached_iff A B P transport tp hOne Kroot E hE rep.1).mpr hOld
    have hNew' : Nonempty (Bridge QB.source KQ q.1) :=
      Eq.mp (congrArg (fun c => Nonempty (Bridge QB.source KQ c)) hClass) hNew
    exact (b j).property hNew'
  have hMixedLegal : Age.Legal QB.source φ.masks mixed allBits := by
    have hp : mixed = old ∘ index := funext hMixed
    have hb : allBits = bits ∘ index := funext hAllBits
    rw [hp,hb]
    exact ⟨fun v => hLegal.1 (index v),fun v w => hLegal.2 (index v) (index w)⟩
  let oldB : Sum (Fin na) (Fin ni) → Sigma B.Point := fun v =>
    match v with
    | Sum.inl i => ⟨(anchor (owners i)).val,
        originalSelectedReachedEclassRepresentative A B P transport hOne Kroot E
          (anchor (owners i)) (points i)⟩
    | Sum.inr j => originalSelectedTaggedRepresentative A B P transport base hBase E (inactivePoints j)
  have hChart : Nonempty
      (OriginalActualNextQuotientChart A B P base hBase E Kroot phase oldB allBits) :=
    (originalRetainedActualSelectedMixedLegal_iff_actualNextChart
      A B P transport tp hOne Kroot phase E hE na ni owners points activeBits inactivePoints
      hMixedInj hInactive).mp hMixedLegal
  obtain ⟨C⟩ := hChart
  let qChart : Sum (Fin na) (Fin ni) → Sigma QN.Point := fun v => πN (C.point v)
  have hQInj : Function.Injective qChart := by
    intro v w h
    apply C.quotient_injective
    let eg := originalSelectedGlobalEClassEquiv A N (P.compose R) hN base hBase E
    have hv := originalCurrentToSelectedPoint_globalE A N (P.compose R) hN base hBase E (C.point v)
    have hw := originalCurrentToSelectedPoint_globalE A N (P.compose R) hN base hBase E (C.point w)
    exact hv.symm.trans ((congrArg eg h).trans hw)
  have hRep (v : Sum (Fin na) (Fin ni)) : πB (oldB v) = old (index v) := by
    cases v with
    | inl i =>
      exact (originalSelectedReachedRepresentative_total_spec A B P transport hOne Kroot E
        (anchor (owners i)) (points i)).trans (hPoint i)
    | inr j =>
      exact originalCurrentToSelectedPoint_representative A B P transport base hBase E (inactivePoints j)
  have hOldParent (v : Sum (Fin na) (Fin ni)) :
      (Quotient.mk'' (oldB v).1 : QB.Sorts) = (old (index v)).1 := by
    cases v with
    | inl i => exact congrArg Sigma.fst (hPoint i)
    | inr j => exact originalOccupancyRepresentative_class A B P base hBase E (inactivePoints j).1
  have hOffset (v : Sum (Fin na) (Fin ni)) :
      originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE (oldB v).1 = 0 := by
    cases v with
    | inl i =>
      exact originalRetainedNamedOffset_anchor_zero A B P transport tp hOne Kroot phase E hE (owners i)
    | inr j =>
      exact originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE
        (oldB (Sum.inr j)).1 (hInactive j)
  have hOwner (v : Sum (Fin na) (Fin ni)) : e (qChart v).1 = (p (index v)).1 := by
    change e (Quotient.mk'' (C.point v).1) = (p (index v)).1
    rw [originalRetainedOccupancyChildEquiv_mk]
    apply UnarySource.childLabel_injective IM
    have hParentName := congrArg Prod.fst (C.names v)
    have hBitName := congrArg Prod.snd (C.names v)
    change (C.point v).1.1 = (oldB v).1 at hParentName
    change (C.point v).1.2.val = allBits v at hBitName
    apply Prod.ext
    · change (Quotient.mk'' (C.point v).1.1 : QB.Sorts) = (p (index v)).1.1
      exact (congrArg (fun i : B.Sorts => (Quotient.mk'' i : QB.Sorts)) hParentName).trans (hOldParent v)
    · change (C.point v).1.2.val +
        originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE (C.point v).1.1 =
        (p (index v)).1.2.val
      have hγ : originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE (C.point v).1.1 = 0 :=
        (congrArg (originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE) hParentName).trans (hOffset v)
      exact (congrArg₂ (fun x y : Bit => x + y) hBitName hγ).trans
        ((add_zero _).trans (hAllBits v))
  have hColour (v w : Sum (Fin na) (Fin ni)) :
      taggedColour QB.source (f (qChart v)) (f (qChart w)) =
        taggedColour QB.source (old (index v)) (old (index w)) := by
    have hv := originalPhaseSelectedPointEquiv_currentToSelected
      A B P transport base hBase E Kroot phase (C.point v)
    have hw := originalPhaseSelectedPointEquiv_currentToSelected
      A B P transport base hBase E Kroot phase (C.point w)
    have hFine := originalCurrentToSelectedPoint_taggedColour_of_eq A B P transport base hBase E
      (oldB v) (oldB w) (R.project (C.point v)) (R.project (C.point w)) (C.fine v w)
    exact (congrArg₂ (taggedColour QB.source) hv hw).trans
      (hFine.trans (congrArg₂ (taggedColour QB.source) (hRep v) (hRep w)))
  let q : Fin n ↪ Sigma QN.Point :=
    ⟨fun i => qChart (index.symm i),hQInj.comp index.symm.injective⟩
  refine ⟨q,?_,?_⟩
  · intro i
    change e (qChart (index.symm i)).1 = (p i).1
    have h := hOwner (index.symm i)
    simpa only [index.apply_symm_apply] using h
  · intro i j
    change taggedColour QB.source (f (qChart (index.symm i))) (f (qChart (index.symm j))) =
      taggedColour QB.source (old i) (old j)
    have h := hColour (index.symm i) (index.symm j)
    simpa only [index.apply_symm_apply] using h

end
end CCO.ExactEPGeometry
