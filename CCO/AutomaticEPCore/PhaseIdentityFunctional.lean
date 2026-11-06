import CCO.AutomaticEPCore.IdentityArrows
import CCO.AutomaticEPCore.IdentityGate
import CCO.ExactEPGeometry.FullReachedOriginalBridge

/-! The SAME actual phase-selected odd arrow at an identity original
gate is a functional involution in the least positive full-exact kernel.
The GateChoice pivot atom is not substituted for the selected arrow. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers
open CCO.ExactEPGeometry CCO.RigidGroupoid.Geometry
noncomputable section

/-- The full bridge theorem and the right adjunction transport actual
dominance to EVERY positive original full-exact equivalence. -/
theorem identity_original_gate_dominant_functional
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b : Reached B.source Kroot)
    (identityGate : PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = ⊥)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b))
    (hne : R ≠ Arrow.id _) (dominant : Dominant _ R) :
    ∃ h : OriginalFunctionalGroup A.G (A.Point (P.parent b.val)),
      h ≠ 1 ∧
      (∀ x y : B.Point b.val,
        R.rel x y ↔ h.val (P.point b.val x) = P.point b.val y) ∧
      ∀ E : ExactEq A.source (P.parent b.val), ⊥ < E →
        ∀ x, E x (h.val x) := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let F := current_kernel_exact_eq B K
  let L := PrefixExactLargestLift.largest A B P transport tp b.val F
  let G := original_largest_gate_kernel A B P transport tp b.val K
  have hL : L = ⊥ := identityGate
  have hLift : PrefixExactRestriction.rho A B P transport b.val L = F :=
    (PrefixExactLargestLift.largest_spec A B P transport tp b.val F).1
  have hG : G.setoid = ⊥ := congrArg (fun E : ExactEq A.source (P.parent b.val) => E.val.val) hL
  have gateTrace (x y : B.Point b.val) :
      G.rel (P.point b.val x) (P.point b.val y) ↔ K.rel x y := by
    change L (P.point b.val x) (P.point b.val y) ↔ F x y
    rw [← PrefixExactRestriction.rho_iff A B P transport b.val L x y,hLift]
  obtain ⟨old,oldTrace⟩ :=
    (full_reached_original_bridge_correspondence
      A B P transport tp hOne Kroot b b).1 R
  have trace (x y : B.Point b.val) :
      old.rel (P.point b.val x) (P.point b.val y) ↔ R.rel x y := by
    simpa using oldTrace x y
  have oldNe : old ≠ Arrow.id G := by
    intro he
    apply hne
    apply Arrow.ext
    funext x y
    apply propext
    rw [← trace x y,he]
    exact gateTrace x y
  obtain ⟨h,graph,hnontrivial⟩ :=
    identity_arrow_functional A.source A.homogeneous G hG old
  refine ⟨h,hnontrivial oldNe,fun x y => (trace x y).symm.trans (graph _ _),?_⟩
  intro E hE
  let Q := PrefixExactRestriction.rho A B P transport b.val E
  let Z : Kernel B.source b.val := ⟨Q.val.val,Q.property⟩
  have hFbot : F = ⊥ := by
    rw [← hLift,hL,PrefixExactRestriction.rho_bot]
  have hKbot : K.setoid = ⊥ := congrArg (fun E : ExactEq B.source b.val => E.val.val) hFbot
  have notLe : ¬ Q ≤ F := by
    intro hQ
    have hEL := (PrefixExactLargestLift.largest_spec A B P transport tp b.val F).2 E |>.mp hQ
    change E ≤ L at hEL
    rw [hL] at hEL
    exact hE.not_ge hEL
  have strict : K < Z := by
    refine lt_iff_le_and_ne.mpr ⟨?_,?_⟩
    · change K.setoid ≤ Z.setoid
      rw [hKbot]
      exact bot_le
    · intro he
      apply notLe
      intro x y hxy
      change K.rel x y
      rw [he]
      exact hxy
  obtain ⟨x₀,y₀,edge⟩ := R.exact.nonempty B.source
  have hOriginal : E (P.point b.val x₀) (h.val (P.point b.val x₀)) := by
    have hz := dominant Z strict x₀ y₀ edge
    have hg : h.val (P.point b.val x₀) = P.point b.val y₀ :=
      (graph _ _).mp ((trace x₀ y₀).mpr edge)
    rw [hg]
    exact hz
  intro x
  obtain ⟨g,hg⟩ := A.source.original_sort_transitive_of_homogeneous
    A.homogeneous (P.parent b.val) (P.point b.val x₀) x
  have invariant := E.property.invariant A.source A.homogeneous
  have hMoved := invariant g _ _ hOriginal
  rw [hg,← h.property g (P.point b.val x₀),hg] at hMoved
  exact hMoved

/-- The h here is selected from phase.atSort itself, so the same h can
subsequently be transported with the actual character-one equation. -/
theorem actual_phase_identity_functional
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
      (∀ x y : B.Point b.val,
        (phase.atSort b).rel x y ↔ h.val (P.point b.val x) = P.point b.val y) ∧
      ∀ x, leastPositiveExact A (P.parent b.val) x (h.val x) := by
  obtain ⟨h,hne,trace,inside⟩ := identity_original_gate_dominant_functional
    A B P transport tp hOne Kroot b identityGate
    (phase.atSort b) (phase.atSort_nonidentity b) (phase.atSort_dominant b)
  refine ⟨h,hne,trace,?_⟩
  intro x
  exact (leastPositiveExact_iff A (P.parent b.val) x (h.val x)).mpr
    (fun E hE => inside E hE x)

end
end CCO.AutomaticEPCore
