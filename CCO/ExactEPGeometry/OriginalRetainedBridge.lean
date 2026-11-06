import CCO.ExactEPGeometry.OriginalRetainedOccupancy
import CCO.ExactEPGeometry.OriginalArrowCurrentExact

/-!
# B062 C77: an E-occupied parent is in the FULL reached component

If an original full RAW-exact equivalence E is below the TRUE selected
original maximal gate G, its individual E-classes hit each supported
current unary type inside the entire G. On an active current parent
the true gate is the corresponding actual restriction of G (C56).
Its trace to the supported target is therefore an actual FULL exact
Bridge, not a hypothetical relation, and the source's canonical
rootArrow makes the target a real object of the FULL reached groupoid.

No source quotient or global automorphism-group section is postulated.
-/ 

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Composition of transports from a common ORIGINAL sort. All
equality proofs are genuine sort equalities, not identifications
of distinct current unary names. -/
theorem original_parent_cast_comp
    {ι : Type u} {X : ι → Type v} {base i j : ι}
    (hbi : base = i) (hbj : base = j) (hij : i = j) (y : X j) :
    (hbi.symm ▸ (hij.symm ▸ y)) = (hbj.symm ▸ y) := by
  cases hbi
  cases hbj
  cases hij
  rfl

/-- A real original FULL-exact equivalence G whose i-restriction is
the ACTUAL gate Ki and which hits every i-point in current target j
constructs a genuine source bridge Ki -> j. The classwise hits will
be supplied below by E<=G and real E occupancy; they are NOT a new
assumption in the final source application. -/
noncomputable def original_full_gate_supported_bridge
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    {i j : B.Sorts} (hij : P.parent i = P.parent j)
    (G : ExactEq A.source (P.parent i))
    (Ki : Kernel B.source i)
    (hGate : ∀ x z : B.Point i,
      G (P.point i x) (P.point i z) ↔ Ki.rel x z)
    (hHit : ∀ x : B.Point i, ∃ y : B.Point j,
      G (P.point i x) (hij.symm ▸ P.point j y)) :
    Bridge B.source Ki j := by
  let R : TRel B.Point i j :=
    fun x y => G (P.point i x) (hij.symm ▸ P.point j y)
  let a : B.Point i := Classical.choice (B.source.nonemptySort i)
  have hReal : ∃ x : B.Point i, ∃ y : B.Point j,
      G (P.point i x) (hij.symm ▸ P.point j y) := by
    obtain ⟨y,hy⟩ := hHit a
    exact ⟨a,y,hy⟩
  have hExact : FullExact B.source R :=
    original_full_exact_nonempty_current_trace
      A B P transport hij (fun x y => G x y) G.property hReal
  refine {
    rel := R
    exact := hExact
    left := ?_
    source := ?_
  }
  · funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact G.val.val.trans ((hGate x z).mpr hxz) hzy
    · intro hxy
      exact ⟨x,Ki.setoid.refl x,hxy⟩
  · funext x z
    apply propext
    constructor
    · rintro ⟨y,hxy,hzy⟩
      exact (hGate x z).mp
        (G.val.val.trans hxy (G.val.val.symm hzy))
    · intro hxz
      obtain ⟨y,hzy⟩ := hHit z
      exact ⟨y,G.val.val.trans ((hGate x z).mpr hxz) hzy,hzy⟩

/-- Real C77 source application: on ANY actual active reached parent
b, each E-supported target j is the target of a FULL current Bridge
from b's actual gate. This discharges BOTH the old-G trace
exactness and the target-seriality premise via the real current
marking prefix and C49 original E-class occupancy. -/
theorem original_retained_supported_type_bridge
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) (j : B.Sorts)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r b.val j) :
    Nonempty (Bridge B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b) j) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Ki := Reached.kernel B.homogeneous C b
  let Gr := PrefixExactLargestLift.largest
    A B P transport tp r (current_kernel_exact_eq B Kroot)
  let Gb := PrefixExactLargestLift.largest
    A B P transport tp b.val (current_kernel_exact_eq B Ki)
  let hbi := hOne (P.parent r) (P.parent b.val)
  let hbj := hOne (P.parent r) (P.parent j)
  let hij := hOne (P.parent b.val) (P.parent j)
  let Gi := oldExactEqCast A.source hbi.symm Gr
  have hRootGate : Gr = oldExactEqCast A.source hbi Gb := by
    have h := original_gates_constant_on_full_reached
      A B P transport tp hOne Kroot (Reached.root Kroot) b
    dsimp only at h
    rw [Reached.root_kernel B.homogeneous C (A := Kroot)] at h
    exact h
  have hLocalGate : Gi = Gb := by
    have h := congrArg (oldExactEqCast A.source hbi.symm) hRootGate
    simpa only [oldExactEqCast_cancel] using h
  have hGate (x z : B.Point b.val) :
      Gi (P.point b.val x) (P.point b.val z) ↔ Ki.rel x z := by
    rw [hLocalGate]
    have hSpec : PrefixExactRestriction.rho A B P transport b.val Gb =
        current_kernel_exact_eq B Ki :=
      (PrefixExactLargestLift.largest_spec
        A B P transport tp b.val (current_kernel_exact_eq B Ki)).1
    calc
      Gb (P.point b.val x) (P.point b.val z) ↔
          (PrefixExactRestriction.rho A B P transport b.val Gb) x z :=
        (PrefixExactRestriction.rho_iff A B P transport b.val Gb x z).symm
      _ ↔ Ki.rel x z := by
        rw [hSpec]
        exact Iff.rfl
  have hHit (x : B.Point b.val) :
      ∃ y : B.Point j,
        Gi (P.point b.val x) (hij.symm ▸ P.point j y) := by
    obtain ⟨y,hxy⟩ :=
      original_retained_each_class_hits_original_gate
        A B P transport tp hOne Kroot E hE b.val j hSupported x
    refine ⟨y,?_⟩
    apply (oldExactEqCast_iff A.source hbi.symm Gr
      (P.point b.val x) (hij.symm ▸ P.point j y)).mpr
    rw [original_parent_cast_comp hbi hbj hij (P.point j y)]
    exact hxy
  exact ⟨original_full_gate_supported_bridge
    A B P transport hij Gi Ki hGate hHit⟩

/-- C77: the full current source's Reached component is closed
under the actual E-occupancy relation when E<=the canonical
original old gate. The intermediate Bridge is genuinely exact;
the root-to-parent Arrow and the represented source calculus
compose it into a genuine Bridge from the selected root. -/
theorem original_retained_occupancy_reaches_target
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (i j : B.Sorts)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r i j)
    (hActive : Nonempty (Bridge B.source Kroot i)) :
    Nonempty (Bridge B.source Kroot j) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let b : Reached B.source Kroot := ⟨i,hActive⟩
  obtain ⟨R⟩ := original_retained_supported_type_bridge
    A B P transport tp hOne Kroot E hE b j hSupported
  let T := Reached.rootArrow B.homogeneous C b
  exact ⟨(T.comp C (R.toArrow B.homogeneous C)).toBridge⟩

/-- Full retained C77 dichotomy on every actual E-occupancy
component: it is wholly active or wholly inactive. This is
an equivalence between REAL Bridge inhabitants, not merely
an assertion about nominal marked child types. -/
theorem original_retained_occupancy_active_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (i j : B.Sorts)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r i j) :
    Nonempty (Bridge B.source Kroot i) ↔
      Nonempty (Bridge B.source Kroot j) := by
  constructor
  · exact original_retained_occupancy_reaches_target
      A B P transport tp hOne Kroot E hE i j hSupported
  · exact original_retained_occupancy_reaches_target
      A B P transport tp hOne Kroot E hE j i
        ((originalExactOccupancySetoid
          A B P (P.parent r) (fun k => hOne (P.parent r) k) E).symm hSupported)

end
end CCO.ExactEPGeometry
