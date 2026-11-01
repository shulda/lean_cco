import CCO.ExactEPGeometry.ActualLabelInduction
import CCO.ExactEPGeometry.CertifiedOriginalKernel
import CCO.ExactEPGeometry.CertifiedGateLabelStep

/-!
# B062 C61: the actual common ORIGINAL exact kernel preserves FINAL names

This proof consumes the ACTUAL finite certified original-gate history:
each selected step retains its very same pivot, actual MaximalGate and
actual SourcePhase. On the unique ORIGINAL sort, a full RAW exact
equivalence E under ALL actual selected old gates is initially
label-compatible. At every selected step, the precisely matching
GateChoice source theorem forces the new phase-bit tags to agree;
the already proven abstract label-induction lemma then transports
COMPLETE names, not merely individual bits.

The actual original sort equality is used ONLY through genuine
dependent casts; no identification of distinct current sorts or
quotient-automorphism section is claimed. The zero-step history has
K_com = original Top and one original sort.

The converse C62–C64 (every original exact label-preserving E lies below
each selected gate) remains a separate actual maximality obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open CCO.ExactEPGeometry.CertifiedGateTower
open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- The actual unary relation of an ORIGINAL full RAW exact
equivalence on the unique original carrier, including both old
tagged endpoints. The equality proof to the fixed original sort
is real, not a section of any quotient action. -/
def originalExactGlobalRelation
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Sigma A.Point → Sigma A.Point → Prop
  | ⟨i,x⟩, ⟨j,y⟩ =>
      E ((hOne i).symm ▸ x) ((hOne j).symm ▸ y)

/-- The genuine ORIGINAL exact-relation restriction on one tagged
current parent is equivalent to the actual old exact-equivalence
transport along the unique original parent name. -/
theorem originalExactGlobalRelation_same_parent
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {j : A.Sorts} (x y : A.Point j) :
    originalExactGlobalRelation A base hOne E ⟨j,x⟩ ⟨j,y⟩ ↔
      (oldExactEqCast A.source (hOne j).symm E) x y :=
  (oldExactEqCast_iff A.source (hOne j).symm E x y).symm

/-- Compatibility of the actual original gate transport with a
SECOND literal old-parent equality. This generic equality proof is
needed in C61: a selected root gate has parent i, whereas every
current parent j may be different, even though i and j both map
back to the ONE original sort. -/
theorem originalExactGlobalRelation_gate_cast
    (S : AtomicSource.{u,v,w} ι X)
    {base i j : ι} (hBaseI : base = i) (hBaseJ : base = j)
    (E : ExactEq S base) (x y : X j) :
    (oldExactEqCast S hBaseI.symm E)
      (((hBaseI.symm.trans hBaseJ).symm) ▸ x)
      (((hBaseI.symm.trans hBaseJ).symm) ▸ y) ↔
    E (hBaseJ.symm ▸ x) (hBaseJ.symm ▸ y) := by
  cases hBaseI
  cases hBaseJ
  exact Iff.rfl

/-- Source C61 on ONE truly selected step, with the SAME GateChoice
used for its SourcePhase, current root and original maximal exact
gate. The old exact E is allowed to be the common exact meet of
many historical gates, or any further exact subequivalence of this
ACTUAL step gate.

Its conclusion preserves the entire next current unary sort name
for every pair in the same original E-class; the proof does not add
a new labelled-source or quotient provider. -/
theorem certifiedStep_original_exact_preserves_labels
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (E : ExactEq A.source base)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step)
    (hBefore : OriginalRelationRespectsLabels s.reduct
      (originalExactGlobalRelation A base hOne E)) :
    OriginalRelationRespectsLabels next.reduct
      (originalExactGlobalRelation A base hOne E) := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hNext : next = CertifiedGateTower.successor s choice :=
    Classical.choose_spec step
  rw [hNext]
  let hBase : base = s.reduct.parent choice.p :=
    hOne (s.reduct.parent choice.p)
  let Eold : ExactEq A.source (s.reduct.parent choice.p) :=
    oldExactEqCast A.source hBase.symm E
  let Gate : ExactEq A.source (s.reduct.parent choice.p) :=
    PrefixExactLargestLift.largest A s.current s.reduct s.transport
      s.product choice.p
      (⟨choice.M.kernel,choice.M.maximal.1.1⟩ :
        ExactEq s.current.source choice.p)
  have hE' : E ≤ oldExactEqCast A.source hBase Gate := by
    exact hE
  have hEold : Eold ≤ Gate := by
    have hCast :=
      oldExactEqCast_mono A.source hBase.symm E
        (oldExactEqCast A.source hBase Gate) hE'
    simpa only [oldExactEqCast_cancel] using hCast
  have hLocal (j : s.current.Sorts)
      (x y : s.current.Point j)
      (hxy : originalExactGlobalRelation A base hOne E
        (s.reduct.project ⟨j,x⟩)
        (s.reduct.project ⟨j,y⟩)) :
      UnarySource.tag (SingleStep.identification s.current choice.phase) j x =
        UnarySource.tag (SingleStep.identification s.current choice.phase) j y := by
    let hBaseJ : base = s.reduct.parent j :=
      hOne (s.reduct.parent j)
    have hRaw : E
        (hBaseJ.symm ▸ s.reduct.point j x)
        (hBaseJ.symm ▸ s.reduct.point j y) := hxy
    have hOld : Eold
        (((hBase.symm.trans hBaseJ).symm) ▸ s.reduct.point j x)
        (((hBase.symm.trans hBaseJ).symm) ▸ s.reduct.point j y) :=
      (originalExactGlobalRelation_gate_cast A.source
        hBase hBaseJ E (s.reduct.point j x)
        (s.reduct.point j y)).mpr hRaw
    exact certified_gatechoice_preserves_next_child_tag
      A s choice
      (fun i j => (hOne i).symm.trans (hOne j))
      Eold hEold j x y hOld
  exact originalRelationRespectsLabels_canonical_step
    s.current s.reduct choice.phase
    (originalExactGlobalRelation A base hOne E) hBefore hLocal

/-- Induction through ALL actual source-certified full-character steps.
No gate is skipped, reselected, or inferred from just a terminal
label. Every step-specific old gate is taken from the TRUE
`certifiedHistoryOriginalGates` list. -/
theorem certifiedHistory_original_exact_preserves_labels
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next)
    (E : ExactEq A.source base)
    (hBound : ∀ G ∈ certifiedHistoryOriginalGates A base hOne history,
      E ≤ G)
    (hStart : OriginalRelationRespectsLabels s.reduct
      (originalExactGlobalRelation A base hOne E)) :
    OriginalRelationRespectsLabels next.reduct
      (originalExactGlobalRelation A base hOne E) := by
  revert hBound hStart
  induction history with
  | nil _ =>
      intro _ hStart
      exact hStart
  | cons step tail ih =>
      intro hBound hStart
      have hStepBound : E ≤ certifiedStepOriginalGate A base hOne step := by
        exact hBound _ (by simp [certifiedHistoryOriginalGates])
      have hTailBound :
          ∀ G ∈ certifiedHistoryOriginalGates A base hOne tail, E ≤ G := by
        intro G hG
        exact hBound G (by simp [certifiedHistoryOriginalGates,hG])
      have hMid :=
        certifiedStep_original_exact_preserves_labels
          A base hOne step E hStepBound hStart
      exact ih hTailBound hMid

/-- Main proved C61 direction at source-original one-sort strength:
the TRUE finite meet of ALL original gates in the actual certified
safe tower preserves EVERY final current unary name. The zero-stage
case is included: the original source has one original sort, so Top
already respects its sole original label.

Unlike a merely postulated gate list, the induction uses the full
genuine certified history and each step's actual same MaximalGate
and SourcePhase. -/
theorem certifiedHistoryCommonOriginalKernel_preserves_final_labels
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal) :
    OriginalRelationRespectsLabels terminal.reduct
      (originalExactGlobalRelation A base hOne
        (certifiedHistoryCommonOriginalKernel A base hOne history)) := by
  let E := certifiedHistoryCommonOriginalKernel A base hOne history
  have hBound :
      ∀ G ∈ certifiedHistoryOriginalGates A base hOne history, E ≤ G :=
    (certifiedHistoryCommonOriginalKernel_greatest A base hOne
      history E).mp le_rfl
  have hInitial : OriginalRelationRespectsLabels
      (CertifiedGateTower.initial A).reduct
      (originalExactGlobalRelation A base hOne E) := by
    exact originalRelationRespectsLabels_zero A.source
      (fun i j => (hOne i).symm.trans (hOne j))
      (originalExactGlobalRelation A base hOne E)
  exact certifiedHistory_original_exact_preserves_labels
    A base hOne history E hBound hInitial

end
end CCO.ExactEPGeometry
