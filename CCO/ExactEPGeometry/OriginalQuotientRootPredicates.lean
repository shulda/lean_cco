import CCO.ExactEPGeometry.CodedCurrentSource
import CCO.ExactEPGeometry.OriginalSelectedGlobalAtomicBlock
import CCO.ExactEPGeometry.OriginalRetainedSelectedSourceIso

/-!
# Fixed original quotient predicates on every actual selected prefix

The code records the VALUE of every original E-saturated binary colour.
All predicates use the same original source A and original full exact E.
The true selected representatives and genuine whole unary reduct supply
their arguments. Complete current quotient colours determine this code,
and both actual successor isomorphisms preserve it literally. In particular
the retained back-and-forth cannot rename the original quotient predicates.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base)

/-- All fixed original E;colour;E predicates, evaluated on the actual
original reduct of the true selected quotient representatives. -/
def originalQuotientRootCode :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    Sigma Q.Point → Sigma Q.Point → (Age.Colour A.source → Prop) :=
  let rep := originalSelectedTaggedRepresentative A B P transport base hOne E
  fun q s a => originalCurrentExactSaturatedColour A A
    (UnaryReduct.identity A.source) base hOne E a
    (P.project (rep q)) (P.project (rep s))

/-- Equality of COMPLETE actual quotient colours preserves the VALUE
of every fixed original E-saturated predicate, not only their partition. -/
theorem originalQuotientRootCode_colour
    (q s q' s' : Sigma
      (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point)
    (h : taggedColour
        (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source q s =
      taggedColour
        (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source q' s') :
    originalQuotientRootCode A B P transport base hOne E q s =
      originalQuotientRootCode A B P transport base hOne E q' s' := by
  let rep := originalSelectedTaggedRepresentative A B P transport base hOne E
  have hBlock := (originalExactSelectedTaggedColour_iff_globalBlock
    A B P transport base hOne E q' s' q s).mp h
  obtain ⟨_,_,x,y,hqx,hColour,hys⟩ := hBlock
  have hOriginal := (unaryReductTaggedColour_iff P
    (rep q') (rep s') x y).mp hColour
  let S := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  have hx : S.r (P.project (rep q)) (P.project x) := hqx
  have hy : S.r (P.project (rep s)) (P.project y) := S.symm hys
  funext a
  apply propext
  exact (setoidSaturation_congr S
    (fun p r => taggedColour A.source p r = a) hx hy).trans
      (originalCurrentExactSaturatedColour_taggedColour_iff
        A A (UnaryReduct.identity A.source) base hOne E a
        (P.project x) (P.project y) (P.project (rep q')) (P.project (rep s'))
        hOriginal.2.2)

variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)

/-- At EVERY actual character step, the natural selected-point map
preserves all fixed original quotient predicates by literal global E-class
equality. This applies to both retained and discarded steps. -/
theorem originalPhaseSelectedPointEquiv_rootCode :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hOne E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hOne E
    ∀ q s : Sigma QN.Point,
      originalQuotientRootCode A B P transport base hOne E (f q) (f s) =
        originalQuotientRootCode A N (P.compose R) hN base hOne E q s := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hOne E
  let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hOne E
  let S := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  dsimp only
  intro q s
  have hq : S.r (P.project (repB (f q))) ((P.compose R).project (repN q)) :=
    originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hOne E q
  have hs : S.r (P.project (repB (f s))) ((P.compose R).project (repN s)) :=
    originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hOne E s
  funext a
  exact propext (setoidSaturation_congr S
    (fun p r => taggedColour A.source p r = a) hq hs)

end

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

/-- The actual retained back-and-forth preserves EVERY fixed original
quotient predicate through the SAME old-reduct projection. Its stronger
common-colour specification, not merely palette equality, supplies the
required equality on the earlier selected quotient. -/
theorem originalRetainedSelectedPointEquiv_rootCode :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let phaseQ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let RM := SingleStep.projection QB phaseQ
    let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
    ∀ q s : Sigma QN.Point,
      originalQuotientRootCode A B P transport base hBase E (RM.project (F q)) (RM.project (F s)) =
        originalQuotientRootCode A N (P.compose R) hN base hBase E q s := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let phaseQ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let RM := SingleStep.projection QB phaseQ
  let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  dsimp only
  intro q s
  have hColour : taggedColour QB.source (RM.project (F q)) (RM.project (F s)) =
      taggedColour QB.source (f q) (f s) :=
    (Classical.choose_spec (originalRetainedSelectedPointEquiv_exists
      A B P transport tp hOne Kroot phase E hE)).2 q s
  exact (originalQuotientRootCode_colour A B P transport base hBase E
    (RM.project (F q)) (RM.project (F s)) (f q) (f s) hColour).trans
      (originalPhaseSelectedPointEquiv_rootCode A B P transport base hBase E Kroot phase q s)

end
end CCO.ExactEPGeometry
