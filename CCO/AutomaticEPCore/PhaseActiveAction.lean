import CCO.AutomaticEPCore.PhaseIdentityFunctional
import CCO.AutomaticEPCore.FunctionalTypes
import CCO.ExactEPGeometry.ActualGateBitPreservation
import CCO.ExactEPGeometry.OriginalGateAllLabels
import CCO.ExactEPGeometry.OriginalDiscardedOccupancy

/-! The actual phase-selected functional involution at an original identity
gate has the SAME full trace on every active current parent. The proof uses
the entire reached connecting Arrow, its original identity-Arrow lift and
commutativity of the original functional group. The phase character then
flips the literal two realized children of each active parent. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.APCharacter.SourceAge
open CCO.ExactEPGeometry CCO.RigidGroupoid.Geometry
noncomputable section

private theorem sortCast_injective {ι : Type u} {X : ι → Type v}
    {i j : ι} (h : i = j) : Function.Injective (fun x : X i => h ▸ x) := by
  cases h
  exact fun _ _ hh => hh

private theorem unaryPoint_injective
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (p : B.Sorts) : Function.Injective (P.point p) := by
  intro x y he
  have hh : (⟨p,x⟩ : Sigma B.Point) = ⟨p,y⟩ := P.bijective.1 (congrArg
    (fun q => (⟨P.parent p,q⟩ : Sigma A.Point)) he)
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh

/-- ALL original functional graphs, including the actual identity,
are complete exact Arrows over real identity. This is the reverse
source direction needed for the full active-orbit assertion. -/
private def functionalIdentityArrow
    (A : CurrentSource.{u,v,w,t}) {i : A.Sorts}
    (K : Kernel A.source i) (hK : K.setoid = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point i)) : Arrow A.source K K where
  rel x y := h.val x = y
  exact := by
    obtain ⟨x₀⟩ := A.source.nonemptySort i
    have graph : A.source.rawAtomRel (A.source.colour x₀ (h.val x₀)) =
        (fun x y => h.val x = y) := by
      funext x y
      exact propext (original_functional_colour_iff A.source A.homogeneous h x₀ x y)
    rw [← graph]
    exact fullExact_actual_atom A.source x₀ (h.val x₀)
  left := by
    change TRel.comp K.setoid.r (fun x y => h.val x = y) = _
    rw [hK]
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      change x = z at hxz
      exact hxz ▸ hzy
    · intro hxy
      exact ⟨x,rfl,hxy⟩
  right := by
    change TRel.comp (fun x y => h.val x = y) K.setoid.r = _
    rw [hK]
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact hxz.trans hzy
    · intro hxy
      exact ⟨y,hxy,rfl⟩
  source := by
    change TRel.comp (fun x y => h.val x = y)
      (TRel.converse (fun x y => h.val x = y)) = K.setoid.r
    rw [hK]
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hyz⟩
      exact h.val.injective (hxz.trans hyz.symm)
    · intro hxy
      change x = y at hxy
      subst y
      exact ⟨h.val x,rfl,rfl⟩
  target := by
    change TRel.comp (TRel.converse (fun x y => h.val x = y))
      (fun x y => h.val x = y) = K.setoid.r
    rw [hK]
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hzx,hzy⟩
      exact hzx.symm.trans hzy
    · intro hxy
      change x = y at hxy
      subst y
      exact ⟨h.val.symm x,h.val.apply_symm_apply x,h.val.apply_symm_apply x⟩

private theorem phase_atSort_transport
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) c)) :
    phase.atSort c = transport
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco)
      (phase.atSort b) R := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let Q := Reached.connectingArrow B.homogeneous C (Reached.root Kroot) b
  have hPath := transport_path_independent C B.homogeneous phase.odd
    (Reached.connectingArrow B.homogeneous C (Reached.root Kroot) c)
    (Q.comp C R)
  change transport C phase.odd _ = transport C (transport C phase.odd Q) R
  rw [hPath]
  unfold transport
  rw [Arrow.inverse_composite]
  simp only [Arrow.comp_assoc]

/-- C47 in real relations: the SAME selected original h, received at b,
is the full trace of the transported actual odd Arrow at EVERY active c.
Only the unique original sort is reindexed; current types stay distinct. -/
theorem actual_phase_identity_same_functional_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)))
    (trace : ∀ x y : B.Point b.val,
      (phase.atSort b).rel x y ↔ h.val (P.point b.val x) = P.point b.val y)
    (c : Reached B.source Kroot) (x y : B.Point c.val) :
    (phase.atSort c).rel x y ↔
      h.val ((hOne (P.parent b.val) (P.parent c.val)).symm ▸ P.point c.val x) =
        ((hOne (P.parent b.val) (P.parent c.val)).symm ▸ P.point c.val y) := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let R := Reached.connectingArrow B.homogeneous C b c
  let G := original_largest_gate_kernel A B P transport tp b.val Kb
  have hG : G.setoid = ⊥ :=
    congrArg (fun E : ExactEq A.source (P.parent b.val) => E.val.val) identityGate
  obtain ⟨old,oldTrace⟩ :=
    (full_reached_original_bridge_correspondence A B P transport tp hOne Kroot b c).1 R
  obtain ⟨g,graph,_⟩ := identity_arrow_functional A.source A.homogeneous G hG old
  have connector (a : B.Point b.val) (z : B.Point c.val) :
      R.rel a z ↔ g.val (P.point b.val a) =
        ((hOne (P.parent b.val) (P.parent c.val)).symm ▸ P.point c.val z) :=
    (oldTrace a z).symm.trans (graph _ _)
  have forward (x y : B.Point c.val) (hxy : (phase.atSort c).rel x y) :
      h.val ((hOne (P.parent b.val) (P.parent c.val)).symm ▸ P.point c.val x) =
        ((hOne (P.parent b.val) (P.parent c.val)).symm ▸ P.point c.val y) := by
    rw [phase_atSort_transport B phase b c R] at hxy
    rcases hxy with ⟨a,hax,a',haa',ha'y⟩
    have hax' := (connector a x).mp hax
    have haa'' := (trace a a').mp haa'
    have ha'y' := (connector a' y).mp ha'y
    have comm := congrArg
      (fun k : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)) =>
        k.val (P.point b.val a))
      (original_functional_mul_comm A.source A.homogeneous h g)
    change h.val (g.val (P.point b.val a)) = g.val (h.val (P.point b.val a)) at comm
    rw [← hax',comm,haa'',ha'y']
  constructor
  · exact forward x y
  · intro hxy
    obtain ⟨z,hxz⟩ := (phase.atSort c).exact.serial B.source B.homogeneous x
    have hxz' := forward x z hxz
    have hOld : P.point c.val z = P.point c.val y := by
      have hh := hxz'.symm.trans hxy
      exact sortCast_injective (hOne (P.parent b.val) (P.parent c.val)).symm hh
    have hCurrent : (⟨c.val,z⟩ : Sigma B.Point) = ⟨c.val,y⟩ :=
      P.bijective.1 (congrArg (fun q => (⟨P.parent c.val,q⟩ : Sigma A.Point)) hOld)
    have hz : z = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hCurrent
    exact hz ▸ hxz

/-- C46–C47: the same original functional graph fixes each active old
type in its ACTUAL support permutation. No marked automorphism is used. -/
theorem actual_phase_identity_active_parent_fixed
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)))
    (trace : ∀ x y : B.Point b.val,
      (phase.atSort b).rel x y ↔ h.val (P.point b.val x) = P.point b.val y)
    (c : Reached B.source Kroot) :
    originalFunctionalTypePerm A B P (P.parent b.val) (hOne (P.parent b.val)) h c.val =
      c.val := by
  apply (original_functional_type_perm_iff A B P (P.parent b.val)
    (hOne (P.parent b.val)) h c.val c.val).mpr
  obtain ⟨x⟩ := B.source.nonemptySort c.val
  obtain ⟨y,hxy⟩ := (phase.atSort c).exact.serial B.source B.homogeneous x
  exact ⟨x,y,(actual_phase_identity_same_functional_trace
    A B P transport tp hOne phase b identityGate h trace c x y).mp hxy⟩

/-- The genuine marked-age mask reads the character-one equation of
phase.atSort itself. This applies to ANY actual reached real odd pair. -/
theorem actual_phase_atSort_mark_add_one
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (c : Reached B.source Kroot) (x y : B.Point c.val)
    (hxy : (phase.atSort c).rel x y) :
    UnarySource.mark (SingleStep.identification B phase) ⟨c.val,y⟩ =
      UnarySource.mark (SingleStep.identification B phase) ⟨c.val,x⟩ + 1 := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let I := SingleStep.identification B phase
  let := Reached.groupoid B.homogeneous C (A := Kroot)
  have legal := (UnarySource.global_marking I).2 ⟨c.val,x⟩ ⟨c.val,y⟩
  have hh := (phase.rigid_mask_iff c c (phase.atSort c) x y hxy
    (UnarySource.mark I ⟨c.val,x⟩) (UnarySource.mark I ⟨c.val,y⟩)).mp legal
  simpa only [phase.atSort_detects c] using hh.2.2

/-- Literal opposite child over an active parent. Both values are valid
and realized by the actual source construction. -/
def phaseActiveOppositeChild
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (c : Reached B.source Kroot)
    (ε : UnarySource.β (SingleStep.identification B phase) c.val) :
    (SingleStep.successor B phase).Sorts :=
  ⟨c.val,⟨ε.val + 1,fun hn => False.elim (hn c.property)⟩⟩

/-- C48: the SAME original h swaps both actual realized children over
EVERY active parent. The selected phase character, rather than an
unrelated GateChoice pivot, supplies the new bit difference one. -/
theorem actual_phase_identity_active_child_image
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)))
    (trace : ∀ x y : B.Point b.val,
      (phase.atSort b).rel x y ↔ h.val (P.point b.val x) = P.point b.val y)
    (c : Reached B.source Kroot)
    (ε : UnarySource.β (SingleStep.identification B phase) c.val) :
    originalFunctionalTypePerm A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent b.val) (hOne (P.parent b.val)) h ⟨c.val,ε⟩ =
        phaseActiveOppositeChild B phase c ε := by
  let I := SingleStep.identification B phase
  obtain ⟨x⟩ := (SingleStep.successor B phase).source.nonemptySort ⟨c.val,ε⟩
  obtain ⟨y,hxy⟩ := (phase.atSort c).exact.serial B.source B.homogeneous x.val
  have bit := actual_phase_atSort_mark_add_one B phase c x.val y hxy
  have tagy : UnarySource.tag I c.val y = (phaseActiveOppositeChild B phase c ε).2 := by
    apply Subtype.ext
    have tagx : UnarySource.mark I ⟨c.val,x.val⟩ = ε.val :=
      congrArg Subtype.val x.property
    change UnarySource.mark I ⟨c.val,y⟩ = ε.val + 1
    exact bit.trans (congrArg (fun q => q + 1) tagx)
  apply (original_functional_type_perm_iff A (SingleStep.successor B phase)
    (P.compose (SingleStep.projection B phase))
    (P.parent b.val) (hOne (P.parent b.val)) h _ _).mpr
  exact ⟨x,⟨y,tagy⟩,(actual_phase_identity_same_functional_trace
    A B P transport tp hOne phase b identityGate h trace c x.val y).mp hxy⟩

/-- Source discharge of C46–C48: one actual phase-selected h belongs
to the SAME least positive full-exact F and swaps both children at
every active parent of THIS step. It may vary between different steps. -/
theorem actual_phase_identity_uniform_child_swap
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = ⊥) :
    ∃ h : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)),
      h ≠ 1 ∧
      (∀ x, leastPositiveExact A (P.parent b.val) x (h.val x)) ∧
      (∀ c : Reached B.source Kroot,
        originalFunctionalTypePerm A B P (P.parent b.val)
          (hOne (P.parent b.val)) h c.val = c.val) ∧
      ∀ (c : Reached B.source Kroot)
        (ε : UnarySource.β (SingleStep.identification B phase) c.val),
        originalFunctionalTypePerm A (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          (P.parent b.val) (hOne (P.parent b.val)) h ⟨c.val,ε⟩ =
            phaseActiveOppositeChild B phase c ε := by
  obtain ⟨h,hne,trace,inside⟩ :=
    actual_phase_identity_functional A B P transport tp hOne phase b identityGate
  exact ⟨h,hne,inside,
    actual_phase_identity_active_parent_fixed A B P transport tp hOne
      phase b identityGate h trace,
    actual_phase_identity_active_child_image A B P transport tp hOne
      phase b identityGate h trace⟩

/-- D09/C39: the ORIGINAL functional subgroup inside exact E is
transitive on every ACTUAL prefix E-occupancy class. This is an induction
assertion, not a source provider or a claim about marked automorphisms. -/
def exactFunctionalPrefixTransitive
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) : Prop :=
  ∀ s t : B.Sorts,
    (originalExactOccupancySetoid A B P base hOne E).r s t →
    ∃ h : functionalSubgroupInside (G := A.G) A.source E,
      originalFunctionalTypePerm A B P base hOne h.val s = t

/-- C39/C42: graph containment preserves each genuine E-occupancy class
at EVERY prefix, including a successor source. -/
theorem exact_functional_type_image_occupancy
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (h : functionalSubgroupInside (G := A.G) A.source E) (s : B.Sorts) :
    (originalExactOccupancySetoid A B P base hOne E).r s
      (originalFunctionalTypePerm A B P base hOne h.val s) := by
  obtain ⟨x,y,hxy⟩ := (original_functional_type_perm_iff A B P base hOne h.val s _).mp rfl
  refine ⟨x,y,?_⟩
  change E (originalPointEquiv A base hOne (P.project ⟨s,x⟩))
    (originalPointEquiv A base hOne (P.project ⟨_,y⟩))
  rw [← hxy]
  exact h.property _

/-- C40: the original one-sort prefix has singleton type occupancy.
The genuine original identity reduct is retained, including finite M. -/
theorem exact_functional_prefix_transitive_initial
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    exactFunctionalPrefixTransitive A A (UnaryReduct.identity A.source) base hOne E := by
  intro s t _
  refine ⟨1,?_⟩
  change originalFunctionalTypePerm A A (UnaryReduct.identity A.source) base hOne 1 s = t
  rw [original_functional_type_perm_one]
  exact initial_type_unique A base hOne s t

/-- C41/C43's actual projection injectivity. In a retained step, two
E-supported children of the SAME parent coincide, by the source theorem
that the true original gate preserves the literal next child tag. -/
theorem retained_exact_occupancy_parent_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (c d : (SingleStep.successor B phase).Sorts)
    (occ : (originalExactOccupancySetoid A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (hOne (P.parent r)) E).r c d)
    (sameParent : c.1 = d.1) : c = d := by
  rcases c with ⟨p,ε⟩
  rcases d with ⟨q,η⟩
  change p = q at sameParent
  subst q
  obtain ⟨x,y,hxy⟩ := occ
  have tag := original_below_largest_preserves_all_next_child
    A B P transport tp hOne Kroot phase E hE p x.val y.val hxy
  have hεη : ε = η := x.property.symm.trans (tag.trans y.property)
  subst η
  rfl

/-- C42–C43: the bound prefix invariant passes through a retained
ACTUAL full-character successor. Movement preserves E-occupancy, the
actual projection is equivariant, and the previous lemma forces the
correct unique lift. No independent child flip is assumed. -/
theorem exact_functional_prefix_transitive_retained
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (previous : exactFunctionalPrefixTransitive A B P
      (P.parent r) (hOne (P.parent r)) E) :
    exactFunctionalPrefixTransitive A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (hOne (P.parent r)) E := by
  intro c d occ
  have oldOcc : (originalExactOccupancySetoid A B P
      (P.parent r) (hOne (P.parent r)) E).r c.1 d.1 := by
    obtain ⟨x,y,hxy⟩ := occ
    exact ⟨x.val,y.val,hxy⟩
  obtain ⟨h,move⟩ := previous c.1 d.1 oldOcc
  refine ⟨h,?_⟩
  let J := originalExactOccupancySetoid A (SingleStep.successor B phase)
    (P.compose (SingleStep.projection B phase))
    (P.parent r) (hOne (P.parent r)) E
  have imageOcc := exact_functional_type_image_occupancy
    A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
    (P.parent r) (hOne (P.parent r)) E h c
  have imageToTarget : J.r
      (originalFunctionalTypePerm A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (hOne (P.parent r)) h.val c) d :=
    J.trans (J.symm imageOcc) occ
  apply retained_exact_occupancy_parent_injective
    A B P transport tp hOne Kroot phase E hE _ d imageToTarget
  exact (original_functional_type_perm_parent A B P (P.parent r)
    (hOne (P.parent r)) (SingleStep.successor B phase)
    (SingleStep.projection B phase) h.val c).trans move

/-- C49–C50: an actual identity-gate step preserves the bound exact-E
orbit invariant for EVERY positive exact E. The discarded-step theorem
gives the actual unchanged occupancy partition. Parent movement is then
corrected, if needed, by the SAME selected phase involution over the
target parent. An inactive parent has its unique valid child. -/
theorem exact_functional_prefix_transitive_identity
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r)) (positive : ⊥ < E)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) = ⊥)
    (previous : exactFunctionalPrefixTransitive A B P
      (P.parent r) (hOne (P.parent r)) E) :
    exactFunctionalPrefixTransitive A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (hOne (P.parent r)) E := by
  classical
  have identityRoot : PrefixExactLargestLift.largest A B P transport tp
      (Reached.root Kroot).val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco)
        (Reached.root Kroot))) = ⊥ := by
    change PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco)
        (Reached.root Kroot))) = ⊥
    rw [Reached.root_kernel]
    exact identityGate
  obtain ⟨odd,_,inside,_,swap⟩ := actual_phase_identity_uniform_child_swap
    A B P transport tp hOne phase (Reached.root Kroot) identityRoot
  let u : functionalSubgroupInside (G := A.G) A.source E :=
    ⟨odd,fun x => leastPositiveExact_le A (P.parent r) E positive (inside x)⟩
  have discarded : ¬ E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) := by
    rw [identityGate]
    exact positive.not_ge
  intro c d occ
  have oldOcc := (original_discarded_successor_occupancy_iff
    A B P transport tp hOne Kroot phase E discarded c d).mp occ
  obtain ⟨h,move⟩ := previous c.1 d.1 oldOcc
  generalize imageEq : originalFunctionalTypePerm A (SingleStep.successor B phase)
    (P.compose (SingleStep.projection B phase))
    (P.parent r) (hOne (P.parent r)) h.val c = image
  have sameParent : image.1 = d.1 := by
    rw [← imageEq]
    exact (original_functional_type_perm_parent A B P (P.parent r)
      (hOne (P.parent r)) (SingleStep.successor B phase)
      (SingleStep.projection B phase) h.val c).trans move
  rcases image with ⟨p,ε⟩
  rcases d with ⟨q,η⟩
  change p = q at sameParent
  subst q
  by_cases hεη : ε = η
  · exact ⟨h,imageEq.trans (congrArg (fun b => (⟨p,b⟩ :
      (SingleStep.successor B phase).Sorts)) hεη)⟩
  · have active : Nonempty (Bridge B.source Kroot p) := by
      by_contra inactive
      exact hεη (Subtype.ext (phase.inactive_bit_unique inactive ε.property η.property))
    let a : Reached B.source Kroot := ⟨p,active⟩
    have different : ε.val ≠ η.val := fun he => hεη (Subtype.ext he)
    have other : η.val = ε.val + (1 : Bit) :=
      (by decide : ∀ a b : Bit, a ≠ b → b = a + (1 : Bit)) _ _ different
    have flipEq : phaseActiveOppositeChild B phase a ε = ⟨p,η⟩ := by
      apply congrArg (fun b => (⟨p,b⟩ : (SingleStep.successor B phase).Sorts))
      exact Subtype.ext other.symm
    refine ⟨u * h,?_⟩
    change originalFunctionalTypePerm A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (hOne (P.parent r)) (u.val * h.val) c = _
    rw [original_functional_type_perm_mul]
    change originalFunctionalTypePerm A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (hOne (P.parent r)) u.val
        (originalFunctionalTypePerm A (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          (P.parent r) (hOne (P.parent r)) h.val c) = _
    rw [imageEq]
    exact (swap a ε).trans flipEq

/-- Fixed ORIGINAL carrier receiving form for the actual retained
step. The old gate is cast only along the unique-original-sort equality;
the current parent names and all real source certificates are retained. -/
theorem exact_functional_prefix_transitive_retained_fixed_base
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source base)
    (hE : E ≤ oldExactEqCast A.source (hOne (P.parent r))
      (PrefixExactLargestLift.largest A B P transport tp r
        (current_kernel_exact_eq B Kroot)))
    (previous : exactFunctionalPrefixTransitive A B P base hOne E) :
    exactFunctionalPrefixTransitive A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) base hOne E := by
  have hBase := hOne (P.parent r)
  cases hBase
  exact exact_functional_prefix_transitive_retained A B P transport tp
    (fun i j => (hOne i).symm.trans (hOne j)) Kroot phase E hE previous

/-- Fixed ORIGINAL carrier receiving form for the actual identity
step. The selected odd involution is constructed from phase.atSort,
and belongs to this SAME positive exact E. -/
theorem exact_functional_prefix_transitive_identity_fixed_base
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source base) (positive : ⊥ < E)
    (identityGate : oldExactEqCast A.source (hOne (P.parent r))
      (PrefixExactLargestLift.largest A B P transport tp r
        (current_kernel_exact_eq B Kroot)) = ⊥)
    (previous : exactFunctionalPrefixTransitive A B P base hOne E) :
    exactFunctionalPrefixTransitive A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) base hOne E := by
  have hBase := hOne (P.parent r)
  cases hBase
  exact exact_functional_prefix_transitive_identity A B P transport tp
    (fun i j => (hOne i).symm.trans (hOne j)) Kroot phase E positive identityGate previous

/-- FULL reverse identity-gate bridge: a real trace of ANY original
functional graph from the root to a current type makes that type reached.
Its current target kernel is constructed as actual equality; the complete
reverse Arrow equations use the accepted displayed-middle product theorem. -/
theorem identity_gate_functional_image_reached
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point (P.parent r)))
    (q : B.Sorts)
    (image : originalFunctionalTypePerm A B P (P.parent r) (hOne (P.parent r)) h r = q) :
    Nonempty (Bridge B.source Kroot q) := by
  let G := original_largest_gate_kernel A B P transport tp r Kroot
  have hG : G.setoid = ⊥ :=
    congrArg (fun E : ExactEq A.source (P.parent r) => E.val.val) identityGate
  let old := functionalIdentityArrow A G hG h
  let Kq : Kernel B.source q := ⟨⊥,fullExact_identity B.source q⟩
  have sourceTrace (x z : B.Point r) :
      G.rel (P.point r x) (P.point r z) ↔ Kroot.rel x z := by
    let F := current_kernel_exact_eq B Kroot
    let L := PrefixExactLargestLift.largest A B P transport tp r F
    have lift : PrefixExactRestriction.rho A B P transport r L = F :=
      (PrefixExactLargestLift.largest_spec A B P transport tp r F).1
    change L (P.point r x) (P.point r z) ↔ F x z
    rw [← PrefixExactRestriction.rho_iff A B P transport r L x z,lift]
  have targetTrace (y z : B.Point q) :
      G.rel ((hOne (P.parent r) (P.parent q)).symm ▸ P.point q y)
        ((hOne (P.parent r) (P.parent q)).symm ▸ P.point q z) ↔ Kq.rel y z := by
    change G.setoid _ _ ↔ y = z
    rw [hG]
    constructor
    · intro hh
      exact unaryPoint_injective A B P q
        (sortCast_injective (hOne (P.parent r) (P.parent q)).symm hh)
    · intro hh
      exact congrArg (fun x => (hOne (P.parent r) (P.parent q)).symm ▸ P.point q x) hh
  obtain ⟨x,y,hxy⟩ := (original_functional_type_perm_iff
    A B P (P.parent r) (hOne (P.parent r)) h r q).mp image
  let R := original_arrow_trace_to_current_arrow A B P transport tp
    (hOne (P.parent r) (P.parent q)) G Kroot Kq sourceTrace targetTrace old ⟨x,y,hxy⟩
  exact ⟨R.toBridge⟩

/-- C44: the ENTIRE active parent set of an original identity-gate
step is precisely ONE orbit of the full original functional group H.
Forward uses the whole current root Arrow; reverse handles every H graph,
including identity, with the actual nonempty current trace. -/
theorem identity_gate_active_iff_functional_orbit
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) = ⊥)
    (q : B.Sorts) :
    Nonempty (Bridge B.source Kroot q) ↔
      ∃ h : OriginalFunctionalGroup A.G (A.Point (P.parent r)),
        originalFunctionalTypePerm A B P (P.parent r) (hOne (P.parent r)) h r = q := by
  constructor
  · intro active
    let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
    let c : Reached B.source Kroot := ⟨q,active⟩
    let R := Reached.rootArrow B.homogeneous C c
    let G := original_largest_gate_kernel A B P transport tp r Kroot
    have hG : G.setoid = ⊥ :=
      congrArg (fun E : ExactEq A.source (P.parent r) => E.val.val) identityGate
    obtain ⟨old,trace⟩ := current_arrow_original_correspondence_trace
      A B P transport tp (hOne (P.parent r) (P.parent q))
      Kroot (Reached.kernel B.homogeneous C c) R
    obtain ⟨h,graph,_⟩ := identity_arrow_functional A.source A.homogeneous G hG old
    obtain ⟨x,y,hxy⟩ := R.exact.nonempty B.source
    refine ⟨h,(original_functional_type_perm_iff
      A B P (P.parent r) (hOne (P.parent r)) h r q).mpr ?_⟩
    exact ⟨x,y,(graph _ _).mp ((trace x y).mpr hxy)⟩
  · rintro ⟨h,image⟩
    exact identity_gate_functional_image_reached
      A B P transport tp hOne Kroot identityGate h q image

/-- The full active H-orbit is preserved by EVERY original functional
element. This uses the actual type action law, not a marked-source action. -/
theorem identity_gate_active_functional_image
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) = ⊥)
    (h : OriginalFunctionalGroup A.G (A.Point (P.parent r)))
    (q : B.Sorts) (active : Nonempty (Bridge B.source Kroot q)) :
    Nonempty (Bridge B.source Kroot
      (originalFunctionalTypePerm A B P (P.parent r) (hOne (P.parent r)) h q)) := by
  obtain ⟨g,image⟩ := (identity_gate_active_iff_functional_orbit
    A B P transport tp hOne Kroot identityGate q).mp active
  apply (identity_gate_active_iff_functional_orbit
    A B P transport tp hOne Kroot identityGate _).mpr
  refine ⟨h * g,?_⟩
  rw [original_functional_type_perm_mul]
  change originalFunctionalTypePerm A B P (P.parent r) (hOne (P.parent r)) h
    (originalFunctionalTypePerm A B P (P.parent r) (hOne (P.parent r)) g r) = _
  rw [image]

/-- C45: under the bound actual prefix invariant, an exact-E occupancy
class is wholly active or wholly inactive. In particular this applies to
the SAME least-positive-exact F and H_F. The stronger full H-orbit result
above proves closure even before using the known normality of H_F. -/
theorem identity_gate_occupancy_active_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot) = ⊥)
    (E : ExactEq A.source (P.parent r))
    (previous : exactFunctionalPrefixTransitive A B P
      (P.parent r) (hOne (P.parent r)) E)
    (p q : B.Sorts)
    (occ : (originalExactOccupancySetoid A B P
      (P.parent r) (hOne (P.parent r)) E).r p q) :
    Nonempty (Bridge B.source Kroot p) ↔ Nonempty (Bridge B.source Kroot q) := by
  constructor
  · intro active
    obtain ⟨h,image⟩ := previous p q occ
    have hh := identity_gate_active_functional_image
      A B P transport tp hOne Kroot identityGate h.val p active
    simpa only [image] using hh
  · intro active
    obtain ⟨h,image⟩ := previous q p
      ((originalExactOccupancySetoid A B P
        (P.parent r) (hOne (P.parent r)) E).symm occ)
    have hh := identity_gate_active_functional_image
      A B P transport tp hOne Kroot identityGate h.val q active
    simpa only [image] using hh

end
end CCO.AutomaticEPCore
