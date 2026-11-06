import CCO.ExactEPGeometry.OriginalActualNextAtomicSaturation
import CCO.ExactEPGeometry.OriginalSelectedGlobalAtomicBlock
import CCO.ExactEPGeometry.OriginalPhaseSelectedPointEquiv

/-!
# B062 C96/C103: complete actual selected successor palette

At ANY genuine character step, the complete NEW selected pair colour is
exactly its TWO new occupancy names and its actual OLD selected colour
under the literal global-E class bijection. This retains the new child
labels; no discarded-case hypothesis is silently used in a retained step.
All old/new atom-block and source providers are discharged internally.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
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

/-- The true old selected owner is the class of the literal parent of
the new canonical representative, for retained AS WELL AS discarded steps. -/
theorem originalPhaseSelectedPointEquiv_owner_formula
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
    (f q).1 = (Quotient.mk'' (R.project (repN q)).1 : OriginalOccupancy A B P base hBase E) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  have hE := originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hBase E q
  have hSupport : (originalExactOccupancySetoid A B P base hBase E).r
      (repB (f q)).1 (R.project (repN q)).1 :=
    ⟨(repB (f q)).2,(R.project (repN q)).2,hE⟩
  exact (originalOccupancyRepresentative_class A B P base hBase E (f q).1).symm.trans
    (Quotient.sound hSupport)

/-- Equal NEW occupancy names have equal genuine OLD occupancy names. -/
theorem originalPhaseSelectedPointEquiv_owner_eq_of_owner_eq
    (q q' : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point)
    (h : q'.1 = q.1) :
    (originalPhaseSelectedPointEquiv A B P transport Kroot phase (P.parent r)
      (fun i => hOne (P.parent r) i) E q').1 =
    (originalPhaseSelectedPointEquiv A B P transport Kroot phase (P.parent r)
      (fun i => hOne (P.parent r) i) E q).1 := by
  have hq := originalPhaseSelectedPointEquiv_owner_formula A B P transport hOne Kroot phase E q
  have hq' := originalPhaseSelectedPointEquiv_owner_formula A B P transport hOne Kroot phase E q'
  dsimp only at hq hq'
  exact hq'.trans ((congrArg
    (fun c => (Quotient.mk'' ((SingleStep.projection B phase).parent
      (originalOccupancyRepresentative A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase)) (P.parent r)
        (fun i => hOne (P.parent r) i) E c)) :
      OriginalOccupancy A B P (P.parent r) (fun i => hOne (P.parent r) i) E)) h).trans hq.symm)

include tp in
/-- At fixed ACTUAL NEW selected occupancy parents, the full NEW atom
block equals the literal OLD selected block under the true class bijection.
The displayed owner equalities are precisely the essential child condition. -/
theorem originalPhaseSelectedAtomicBlock_iff_of_owner_eq
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point)
    (hq : q'.1 = q.1) (hs : s'.1 = s.1) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
    let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
    originalCurrentExactSaturatedColour A N (P.compose R) base hBase E
      (taggedColour N.source (repN q) (repN s)) (repN q') (repN s') ↔
    originalCurrentExactSaturatedColour A B P base hBase E
      (taggedColour B.source (repB (f q)) (repB (f s))) (repB (f q')) (repB (f s')) := by
  rcases q with ⟨c,x⟩
  rcases s with ⟨d,y⟩
  rcases q' with ⟨c',x'⟩
  rcases s' with ⟨d',y'⟩
  dsimp only at hq hs
  subst c'
  subst d'
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  let T := currentOriginalExactSetoid A B P base hBase E
  have hGlobal (p : Sigma (originalExactSelectedQuotientCurrentSource
      A N (P.compose R) hN base hBase E).Point) :
      T.r (repB (f p)) (R.project (repN p)) :=
    originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hBase E p
  have hNext := originalActualNextAtomicSaturation_iff A B P transport tp hOne Kroot phase E
    (repN ⟨c,x⟩).2 (repN ⟨c,x'⟩).2 (repN ⟨d,y⟩).2 (repN ⟨d,y'⟩).2
  have hSeed := originalCurrentExactAtomicBlock_seed_congr A B P base hBase E
    (R.project (repN ⟨c,x⟩)) (R.project (repN ⟨d,y⟩))
    (repB (f ⟨c,x⟩)) (repB (f ⟨d,y⟩))
    (R.project (repN ⟨c,x'⟩)) (R.project (repN ⟨d,y'⟩))
    (T.symm (hGlobal ⟨c,x⟩)) (T.symm (hGlobal ⟨d,y⟩))
  have hEndpoints := setoidSaturation_congr T
    (fun a b => taggedColour B.source a b = taggedColour B.source (repB (f ⟨c,x⟩)) (repB (f ⟨d,y⟩)))
    (T.symm (hGlobal ⟨c,x'⟩)) (T.symm (hGlobal ⟨d,y'⟩))
  exact hNext.trans (hSeed.trans hEndpoints)

include tp in
/-- The COMPLETE genuinely realized NEW selected atomic palette is
exactly BOTH new occupancy names plus the actual OLD quotient pair colour.
Logical identity and every mixed named pair are included. -/
theorem originalPhaseSelectedTaggedColour_iff
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    taggedColour QN.source q' s' = taggedColour QN.source q s ↔
      q'.1 = q.1 ∧ s'.1 = s.1 ∧
      taggedColour QB.source (f q') (f s') = taggedColour QB.source (f q) (f s) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  have hNew := originalExactSelectedTaggedColour_iff_globalBlock A N (P.compose R) hN base hBase E q s q' s'
  have hOld := originalExactSelectedTaggedColour_iff_globalBlock A B P transport base hBase E
    (f q) (f s) (f q') (f s')
  constructor
  · intro h
    obtain ⟨hq,hs,hBlock⟩ := hNew.mp h
    exact ⟨hq,hs,hOld.mpr
      ⟨originalPhaseSelectedPointEquiv_owner_eq_of_owner_eq A B P transport hOne Kroot phase E q q' hq,
       originalPhaseSelectedPointEquiv_owner_eq_of_owner_eq A B P transport hOne Kroot phase E s s' hs,
       (originalPhaseSelectedAtomicBlock_iff_of_owner_eq A B P transport tp hOne Kroot phase E
         q s q' s' hq hs).mp hBlock⟩⟩
  · rintro ⟨hq,hs,h⟩
    exact hNew.mpr ⟨hq,hs,
      (originalPhaseSelectedAtomicBlock_iff_of_owner_eq A B P transport tp hOne Kroot phase E
        q s q' s' hq hs).mpr (hOld.mp h).2.2⟩

end
end CCO.ExactEPGeometry
