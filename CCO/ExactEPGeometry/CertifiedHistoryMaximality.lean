import CCO.ExactEPGeometry.CertifiedFinalKernelSupport
import CCO.ExactEPGeometry.OldGateBitMaximality

/-!
# B062 C62–C64: the GREATEST original FULL RAW-exact final-label kernel

A REAL unary reduct is bijective on the entire current old carrier.
Therefore a final sort-label condition pulls back through any preceding
actual unary refinement, without selecting imaginary quotient points
or assuming a section of an automorphism group.

In a genuine full AP-only `CertifiedGateTower.Step`, all current
points have a literal canonical successor child named by their
ACTUAL legal SourcePhase bit. If the FINAL labels identify every
pair of an original FULL RAW-exact equivalence E, then these actual
next bits must agree on E-pairs at the selected root. The proved C62
odd-Arrow dominance and E1/E2/E3 right adjoint yield E <= the SAME
original GateChoice gate selected in the real history.

A backward induction over EVERY such step proves that ANY original
FULL RAW-exact E preserving all final unary type names lies below
each real historical gate. Since the common K_com is the ACTUAL
finite ExactEq meet of those same gates (empty list means Top),
it is precisely the GREATEST original FULL RAW-exact relation
preserving every final unary label, including zero-step histories.

No stronger source premise, quotient SAP, group section, or false
identity-of-real-points conclusion is introduced.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open CCO.ExactEPGeometry.CertifiedGateTower
open RigidGroupoid.Geometry

noncomputable section

variable {ι κ ν : Type u}
variable {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}

/-- If an actual original relation respects every FINAL unary name,
it respects the preceding current type names as well. The preimages
of two old current points are provided by the ACTUAL whole-carrier
bijection of Q, not a hypothetical quotient-action section. -/
theorem originalRelationRespectsLabels_comp_backward
    (P : UnaryReduct S T) (Q : UnaryReduct T U)
    (R : Sigma X → Sigma X → Prop)
    (hAfter : OriginalRelationRespectsLabels (P.compose Q) R) :
    OriginalRelationRespectsLabels P R := by
  intro a b hab
  obtain ⟨a',ha⟩ := Q.bijective.2 a
  obtain ⟨b',hb⟩ := Q.bijective.2 b
  have ha' : Q.project a' = a := ha
  have hb' : Q.project b' = b := hb
  have hFinal :
      R ((P.compose Q).project a') ((P.compose Q).project b') := by
    change R (P.project (Q.project a')) (P.project (Q.project b'))
    rw [ha',hb']
    exact hab
  have hNames := hAfter a' b' hFinal
  have hParent := congrArg Q.parent hNames
  change (Q.project a').1 = (Q.project b').1 at hParent
  rwa [ha',hb'] at hParent

/-- A true canonical successor contains a REAL child point for
EVERY current parent point: its child name uses precisely that
point's actual pulled-back valid bit. A final-label equality on
such two child points therefore forces their literal current
valid phase tags to be equal, not merely equiorbital. -/
theorem originalRelationRespectsLabels_canonical_step_backward_bit
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    {i : B.Sorts} {K : Kernel B.source i}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (R : Sigma A.Point → Sigma A.Point → Prop)
    (hAfter : OriginalRelationRespectsLabels
      (P.compose (SingleStep.projection B phase)) R)
    (j : B.Sorts) (x y : B.Point j)
    (hxy : R (P.project ⟨j,x⟩) (P.project ⟨j,y⟩)) :
    UnarySource.tag (SingleStep.identification B phase) j x =
      UnarySource.tag (SingleStep.identification B phase) j y := by
  let I := SingleStep.identification B phase
  let Q := SingleStep.projection B phase
  let a : Sigma (SingleStep.successor B phase).Point :=
    ⟨⟨j,UnarySource.tag I j x⟩,⟨x,rfl⟩⟩
  let b : Sigma (SingleStep.successor B phase).Point :=
    ⟨⟨j,UnarySource.tag I j y⟩,⟨y,rfl⟩⟩
  have hQa : Q.project a = ⟨j,x⟩ := rfl
  have hQb : Q.project b = ⟨j,y⟩ := rfl
  have hRelation :
      R ((P.compose Q).project a) ((P.compose Q).project b) := by
    change R (P.project (Q.project a)) (P.project (Q.project b))
    rw [hQa,hQb]
    exact hxy
  have hNames := hAfter a b hRelation
  have hChildren :
      (⟨j,UnarySource.tag I j x⟩ : Sigma (UnarySource.β I)) =
      ⟨j,UnarySource.tag I j y⟩ := hNames
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hChildren

/-- C62: for a REAL selected original-gate-certified Step, a
source-original FULL RAW-exact E whose classes have the SAME next
current labels lies below that selected step's greatest original
exact gate. Furthermore the label compatibility already holds at
the PRECEDING actual source.

The only original one-sort premise is explicit; current sorts and
their genuinely different child tags remain distinct. -/
theorem certifiedStep_original_exact_labels_force_gate
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (E : ExactEq A.source base)
    (hAfter : OriginalRelationRespectsLabels next.reduct
      (originalExactGlobalRelation A base hOne E)) :
    OriginalRelationRespectsLabels s.reduct
        (originalExactGlobalRelation A base hOne E) ∧
      E ≤ certifiedStepOriginalGate A base hOne step := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hNext : next = CertifiedGateTower.successor s choice :=
    Classical.choose_spec step
  rw [hNext] at hAfter
  let R := originalExactGlobalRelation A base hOne E
  let Q := SingleStep.projection s.current choice.phase
  have hAfter' : OriginalRelationRespectsLabels (s.reduct.compose Q) R := by
    simpa only [CertifiedGateTower.successor] using hAfter
  have hBefore : OriginalRelationRespectsLabels s.reduct R :=
    originalRelationRespectsLabels_comp_backward s.reduct Q R hAfter'
  let hBase : base = s.reduct.parent choice.p :=
    hOne (s.reduct.parent choice.p)
  let Eold : ExactEq A.source (s.reduct.parent choice.p) :=
    oldExactEqCast A.source hBase.symm E
  let Gate : ExactEq A.source (s.reduct.parent choice.p) :=
    PrefixExactLargestLift.largest A s.current s.reduct
      s.transport s.product choice.p
      (⟨choice.M.kernel,choice.M.maximal.1.1⟩ :
        ExactEq s.current.source choice.p)
  have hRootLabels (x y : s.current.Point choice.p)
      (hxy : Eold (s.reduct.point choice.p x)
        (s.reduct.point choice.p y)) :
      UnarySource.tag (SingleStep.identification s.current choice.phase)
        choice.p x =
      UnarySource.tag (SingleStep.identification s.current choice.phase)
        choice.p y := by
    have hE : E
        (hBase.symm ▸ s.reduct.point choice.p x)
        (hBase.symm ▸ s.reduct.point choice.p y) :=
      (oldExactEqCast_iff A.source hBase.symm E
        (s.reduct.point choice.p x)
        (s.reduct.point choice.p y)).mp hxy
    have hR : R (s.reduct.project ⟨choice.p,x⟩)
        (s.reduct.project ⟨choice.p,y⟩) := by
      change E
        ((hOne (s.reduct.parent choice.p)).symm ▸
          s.reduct.point choice.p x)
        ((hOne (s.reduct.parent choice.p)).symm ▸
          s.reduct.point choice.p y)
      exact hE
    exact originalRelationRespectsLabels_canonical_step_backward_bit
      A s.current s.reduct choice.phase R
      hAfter' choice.p x y hR
  have hEoldBound : Eold ≤ Gate :=
    certified_gatechoice_original_exact_label_le_gate
      A s choice Eold hRootLabels
  have hCastBound :
      oldExactEqCast A.source hBase Eold ≤
        oldExactEqCast A.source hBase Gate :=
    oldExactEqCast_mono A.source hBase Eold Gate hEoldBound
  have hStepBound : E ≤ certifiedStepOriginalGate
      A base hOne step := by
    change E ≤ oldExactEqCast A.source hBase Gate
    simpa only [Eold,oldExactEqCast_cancel] using hCastBound
  exact ⟨hBefore,hStepBound⟩

/-- C62–C64 BACKWARD induction over ALL actual safe steps. Any
original exact equivalence respecting final names also respects the
starting names and lies below EVERY genuine selected old gate.
The induction does not infer a step gate from its final rank. -/
theorem certifiedHistory_original_exact_labels_force_all_gates
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {s terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s terminal)
    (E : ExactEq A.source base)
    (hFinal : OriginalRelationRespectsLabels terminal.reduct
      (originalExactGlobalRelation A base hOne E)) :
    OriginalRelationRespectsLabels s.reduct
        (originalExactGlobalRelation A base hOne E) ∧
      ∀ G ∈ certifiedHistoryOriginalGates A base hOne history, E ≤ G := by
  revert hFinal
  induction history with
  | nil _ =>
      intro hFinal
      refine ⟨hFinal,?_⟩
      intro G hG
      cases hG
  | cons step tail ih =>
      intro hFinal
      obtain ⟨hIntermediate,hTailBound⟩ := ih hFinal
      obtain ⟨hBefore,hStepBound⟩ :=
        certifiedStep_original_exact_labels_force_gate
          A base hOne step E hIntermediate
      refine ⟨hBefore,?_⟩
      intro G hG
      change G ∈ certifiedStepOriginalGate A base hOne step ::
        certifiedHistoryOriginalGates A base hOne tail at hG
      rcases List.mem_cons.mp hG with hHead | hTail
      · subst G
        exact hStepBound
      · exact hTailBound G hTail

/-- C64 converse: ANY original FULL RAW-exact equivalence whose real
classes never cross a final current unary type lies BELOW the
ACTUAL common historical original exact gate. No final-label
invariance is assumed for nonexact original equivalences. -/
theorem certifiedHistory_preserving_final_labels_le_common_kernel
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal)
    (E : ExactEq A.source base)
    (hFinal : OriginalRelationRespectsLabels terminal.reduct
      (originalExactGlobalRelation A base hOne E)) :
    E ≤ certifiedHistoryCommonOriginalKernel A base hOne history := by
  have hAll :=
    (certifiedHistory_original_exact_labels_force_all_gates
      A base hOne history E hFinal).2
  exact (certifiedHistoryCommonOriginalKernel_greatest
    A base hOne history E).mpr hAll

/-- The full C61–C64 **largest original exact label kernel**
characterization at the genuine finite source-certified history:
the original exact E has all classes contained in final REALIZED
unary types iff it lies below the true historical finite gate meet.
Includes repeated gate steps and a zero-stage Top source.

This is a statement about the FULL RAW-exact sublattice, not an
assertion that every invariant relation is exact, or that the old
common kernel equals pointwise identity. -/
theorem certifiedHistory_common_kernel_largest_exact_labels
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal)
    (E : ExactEq A.source base) :
    E ≤ certifiedHistoryCommonOriginalKernel A base hOne history ↔
      OriginalRelationRespectsLabels terminal.reduct
        (originalExactGlobalRelation A base hOne E) := by
  constructor
  · intro hE
    have hK :
        OriginalRelationRespectsLabels terminal.reduct
          (originalExactGlobalRelation A base hOne
            (certifiedHistoryCommonOriginalKernel A base hOne history)) :=
      certifiedHistoryCommonOriginalKernel_preserves_final_labels
        A base hOne history
    rintro ⟨i,x⟩ ⟨j,y⟩ hxy
    apply hK ⟨i,x⟩ ⟨j,y⟩
    change (certifiedHistoryCommonOriginalKernel A base hOne history)
      ((hOne (terminal.reduct.parent i)).symm ▸ terminal.reduct.point i x)
      ((hOne (terminal.reduct.parent j)).symm ▸ terminal.reduct.point j y)
    exact hE hxy
  · exact certifiedHistory_preserving_final_labels_le_common_kernel
      A base hOne history E

end
end CCO.ExactEPGeometry
