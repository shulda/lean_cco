import CCO.ExactEPGeometry.OriginalRetainedActualSelectedMasks
import CCO.ExactEPGeometry.OriginalRetainedBothGraphs
import CCO.ExactEPGeometry.OriginalRetainedInactiveGraph

/-!
# B062 C81/C103: true retained occupancy names are actual selected child names

An actual old child (j,epsilon) receives the literal selected parent [j]
and the corrected bit epsilon+gamma_j. Here gamma_j is the already proved
actual full-character offset when j is reached, and zero when it is
inactive. The source offset-graph theorem proves that equality of these
actual child names is EXACTLY original E-occupancy of the old children.
Every actual selected child name has a genuine old child preimage.

This is an equivalence of the actual SORT sets only. Canonical point
markings of the two separately constructed homogeneous limits need not
coincide; no point/source isomorphism is asserted by this module.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry RigidGroupoid.Phase
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

/-- The true C84 offset extended to all named parents by the required
inactive zero convention. Only actually reached objects receive a phase. -/
def originalRetainedNamedOffset (j : B.Sorts) : Bit := by
  classical
  exact if hj : Nonempty (Bridge B.source Kroot j) then
    originalReachedGlobalOffset A B P transport tp hOne Kroot phase E hE ⟨j,hj⟩
  else 0

theorem originalRetainedNamedOffset_active (b : Reached B.source Kroot) :
    originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE b.val =
    originalReachedGlobalOffset A B P transport tp hOne Kroot phase E hE b := by
  classical
  simp only [originalRetainedNamedOffset,dif_pos b.property]
  apply congrArg (originalReachedGlobalOffset A B P transport tp hOne Kroot phase E hE)
  apply Subtype.ext
  rfl

theorem originalRetainedNamedOffset_inactive (j : B.Sorts)
    (hj : ¬Nonempty (Bridge B.source Kroot j)) :
    originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE j = 0 := by
  classical
  simp only [originalRetainedNamedOffset,dif_neg hj]

/-- Literal corrected labeling of each actual old successor child by a
valid actual child of the retained selected SourcePhase. -/
def originalRetainedChildToSelectedChild
    (c : (SingleStep.successor B phase).Sorts) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport
      (P.parent r) (fun i => hOne (P.parent r) i) E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    (SingleStep.successor Q φ).Sorts := by
  let Q := originalExactSelectedQuotientCurrentSource A B P transport
    (P.parent r) (fun i => hOne (P.parent r) i) E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let z := c.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE c.1
  refine ⟨Quotient.mk'' c.1,⟨z,?_⟩⟩
  change φ.validBit (Quotient.mk'' c.1) z
  apply (originalRetainedActualSelectedPhase_validBit_iff
    A B P transport tp hOne Kroot phase E hE c.1 z).mpr
  intro hInactive
  dsimp only [z]
  rw [originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE c.1 hInactive,
    add_zero]
  exact c.2.property hInactive

theorem originalRetainedChildToSelectedChild_parent
    (c : (SingleStep.successor B phase).Sorts) :
    (originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE c).1 =
      (Quotient.mk'' c.1 : OriginalOccupancy A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E) := rfl

theorem originalRetainedChildToSelectedChild_bit
    (c : (SingleStep.successor B phase).Sorts) :
    (originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE c).2.val =
      c.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE c.1 := rfl

theorem originalRetainedChildToSelectedChild_bit_active
    (b : Reached B.source Kroot)
    (ε : UnarySource.β (SingleStep.identification B phase) b.val) :
    (originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE ⟨b.val,ε⟩).2.val =
      ε.val + originalReachedGlobalOffset A B P transport tp hOne Kroot phase E hE b := by
  exact congrArg (fun z => ε.val + z)
    (originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE b)

theorem originalRetainedChildToSelectedChild_bit_inactive
    (c : (SingleStep.successor B phase).Sorts)
    (hInactive : ¬Nonempty (Bridge B.source Kroot c.1)) :
    (originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE c).2.val = 0 := by
  change c.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE c.1 = 0
  rw [originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE c.1 hInactive,
    c.2.property hInactive,zero_add]

/-- On a genuinely occupied old component, equality of the corrected
bits is precisely actual successor E-occupancy. This includes inactive
components with their single prescribed zero bit. -/
theorem originalRetainedChildren_correctedBit_iff
    (c d : (SingleStep.successor B phase).Sorts)
    (hOld : (originalExactOccupancySetoid A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E).r c.1 d.1) :
    (originalExactOccupancySetoid A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).r c d ↔
    c.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE c.1 =
      d.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE d.1 := by
  classical
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let J := originalExactOccupancySetoid A B P base hBase E
  let CB := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous CB (A := Kroot)
  by_cases hc : Nonempty (Bridge B.source Kroot c.1)
  · have hd : Nonempty (Bridge B.source Kroot d.1) :=
      (original_retained_occupancy_active_iff A B P transport tp hOne Kroot E hE
        c.1 d.1 hOld).mp hc
    let b : Reached B.source Kroot := ⟨c.1,hc⟩
    let q : Reached B.source Kroot := ⟨d.1,hd⟩
    let anchor := originalReachedOccupancyAnchorOf A B P base hBase E Kroot
    let a := anchor b
    have hba : J.r b.val a.val :=
      originalReachedOccupancyAnchorOf_supported A B P base hBase E Kroot b
    have hqa : J.r q.val a.val := J.trans (J.symm hOld) hba
    have hAnchor : anchor b = anchor q :=
      originalReachedOccupancyAnchorOf_eq A B P base hBase E Kroot b q hOld
    have gb : originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE b.val =
        phase.character.value
          (original_retained_identity_arrow A B P transport tp hOne Kroot E hE b a hba) := by
      rw [originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE b]
      exact originalRetainedAnchorOffset_supported A B P transport tp hOne Kroot phase E hE a b hba
    have gq : originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE q.val =
        phase.character.value
          (original_retained_identity_arrow A B P transport tp hOne Kroot E hE q a hqa) := by
      rw [originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE q]
      change originalRetainedAnchorOffset A B P transport tp hOne Kroot phase E hE (anchor q) q = _
      rw [← hAnchor]
      exact originalRetainedAnchorOffset_supported A B P transport tp hOne Kroot phase E hE a q hqa
    have h := original_retained_children_offset_graph_iff A B P transport tp hOne
      Kroot phase E hE a b q hba hqa c.2 d.2
    erw [← gb,← gq] at h
    exact h
  · have hd : ¬Nonempty (Bridge B.source Kroot d.1) := by
      intro hActive
      exact hc ((original_retained_occupancy_active_iff A B P transport tp hOne
        Kroot E hE c.1 d.1 hOld).mpr hActive)
    have hNext := (original_retained_inactive_successor_occupancy_iff
      A B P transport tp hOne Kroot phase E hE c d hc).mpr hOld
    have hBits : c.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE c.1 =
        d.2.val + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE d.1 := by
      rw [originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE c.1 hc,
        originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE d.1 hd,
        c.2.property hc,d.2.property hd]
    exact ⟨fun _ => hBits,fun _ => hNext⟩

/-- Equality of the ACTUAL selected successor names is exactly the
original E-support setoid on actual old successor child names. -/
theorem originalRetainedChildToSelectedChild_eq_iff
    (c d : (SingleStep.successor B phase).Sorts) :
    originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE c =
      originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE d ↔
    (originalExactOccupancySetoid A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).r c d := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let f := originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE
  constructor
  · intro h
    have hParent : (Quotient.mk'' c.1 : OriginalOccupancy A B P base hBase E) = Quotient.mk'' d.1 :=
      congrArg (fun z => z.1) h
    have hOld : (originalExactOccupancySetoid A B P base hBase E).r c.1 d.1 := Quotient.exact hParent
    have hBit := congrArg (fun z : (SingleStep.successor Q φ).Sorts => z.2.val) h
    exact (originalRetainedChildren_correctedBit_iff A B P transport tp hOne
      Kroot phase E hE c d hOld).mpr hBit
  · intro h
    have hOld : (originalExactOccupancySetoid A B P base hBase E).r c.1 d.1 := by
      obtain ⟨x,y,hxy⟩ := h
      exact ⟨x.val,y.val,hxy⟩
    have hBit := (originalRetainedChildren_correctedBit_iff A B P transport tp hOne
      Kroot phase E hE c d hOld).mp h
    apply UnarySource.childLabel_injective (SingleStep.identification Q φ)
    exact Prod.ext (Quotient.sound hOld) hBit

/-- Every valid ACTUAL selected child has a true old child preimage.
In particular both active bits occur, while the inactive bit stays zero. -/
theorem originalRetainedChildToSelectedChild_surjective :
    Function.Surjective (originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  intro q
  let j := originalOccupancyRepresentative A B P base hBase E q.1
  have hj : (Quotient.mk'' j : OriginalOccupancy A B P base hBase E) = q.1 :=
    originalOccupancyRepresentative_class A B P base hBase E q.1
  let γ := originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE j
  have hValidQ : φ.validBit (Quotient.mk'' j) q.2.val :=
    Eq.mpr (congrArg (fun s => φ.validBit s q.2.val) hj) q.2.property
  have hValidB : phase.validBit j (q.2.val + γ) := by
    intro hInactive
    have hZero : q.2.val = 0 := (originalRetainedActualSelectedPhase_validBit_iff
      A B P transport tp hOne Kroot phase E hE j q.2.val).mp hValidQ hInactive
    have hγ : γ = 0 := originalRetainedNamedOffset_inactive
      A B P transport tp hOne Kroot phase E hE j hInactive
    rw [hZero,hγ,zero_add]
  let ε : UnarySource.β (SingleStep.identification B phase) j := ⟨q.2.val + γ,hValidB⟩
  let c : (SingleStep.successor B phase).Sorts := ⟨j,ε⟩
  refine ⟨c,?_⟩
  apply UnarySource.childLabel_injective (SingleStep.identification Q φ)
  apply Prod.ext hj
  change (q.2.val + γ) + γ = q.2.val
  have hDouble : ∀ z : Bit, z + z = 0 := by decide
  rw [add_assoc,hDouble,add_zero]

/-- True retained C103 sort equivalence. The domain is the actual
original-E occupancy quotient of the actual old successor sort set;
the codomain is the ACTUAL selected SourcePhase's child sort set. -/
def originalRetainedOccupancyChildEquiv :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    OriginalOccupancy A N (P.compose R) base hBase E ≃ (SingleStep.successor Q φ).Sorts := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let S := originalExactOccupancySetoid A N (P.compose R) base hBase E
  let f := originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE
  let fq : Quotient S → _ := Quotient.lift f (fun c d h =>
    (originalRetainedChildToSelectedChild_eq_iff A B P transport tp hOne Kroot phase E hE c d).mpr h)
  apply Equiv.ofBijective fq
  constructor
  · intro c d h
    induction c using Quotient.inductionOn with
    | _ c =>
      induction d using Quotient.inductionOn with
      | _ d =>
        exact Quotient.sound ((originalRetainedChildToSelectedChild_eq_iff
          A B P transport tp hOne Kroot phase E hE c d).mp h)
  · intro q
    obtain ⟨c,hc⟩ := originalRetainedChildToSelectedChild_surjective
      A B P transport tp hOne Kroot phase E hE q
    exact ⟨Quotient.mk'' c,hc⟩

/-- Literal parent projection on actual original E-occupancy classes.
Forward support projects the real E-related pair; no converse is used. -/
def originalRetainedOccupancyParentMap :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    OriginalOccupancy A N (P.compose R) base hBase E →
      OriginalOccupancy A B P base hBase E := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  exact Quotient.map R.parent (fun {c d} h => by
    obtain ⟨x,y,hxy⟩ := h
    exact ⟨R.point c x,R.point d y,hxy⟩)

/-- The sort equivalence sends each literal child class to the
specified corrected actual child name, before any point choices. -/
theorem originalRetainedOccupancyChildEquiv_mk
    (c : (SingleStep.successor B phase).Sorts) :
    originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE (Quotient.mk'' c) =
      originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE c := rfl

/-- Its first component is EXACTLY the quotient map of the true unary
reduct parent projection, on EVERY actual next occupancy class. -/
theorem originalRetainedOccupancyChildEquiv_parent
    (c : OriginalOccupancy A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E) :
    (originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE c).1 =
      originalRetainedOccupancyParentMap A B P hOne Kroot phase E c := by
  induction c using Quotient.inductionOn with
  | _ c => rfl

end
end CCO.ExactEPGeometry
