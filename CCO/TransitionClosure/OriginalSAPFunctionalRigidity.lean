import CCO.QuotientTransport.Consumers
import CCO.StabilizerSAP
import CCO.SAPPoint

/-!
# B049 source07 C24-C30: no nonidentity real functional transition under old SAP

An invariant original real relation that is functional in its target
cannot have an edge to a DIFFERENT original tagged point. Otherwise
the real OLD stabilizer of its input moves the output outside any
prescribed finite forbidden set, contradicting functionality.

The proof uses the actual original age SAP and homogeneity, not
definability in a quotient reduct, quotient SAP, hidden SAP, CCO,
an assumed algebraic-closure predicate, or faithfulness of G.

This applies across different original sorts as well as on one sort.
The generic B040 transport construction is only used for the
consequence when the induced target quotient kernel is equality.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

/-- Source07 C24 original SAP real rigidity:
an invariant typed binary relation R that is functional on its
target has ONLY literal ORIGINAL identity edges, between the SAME
named sort and SAME point. A hypothetical edge to a different
tagged target would give infinitely many images by the ACTUAL
source stabilizer's fresh orbit, contradicting functionality.
No 0-definability or source CCO is needed for this stronger result. -/
theorem original_SAP_invariant_function_edge_is_identity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (R : X i → X j → Prop)
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hFunctional : ∀ x : X i, ∀ y z : X j,
      R x y → R x z → y = z)
    (x : X i) (y : X j) (hR : R x y) :
    (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  classical
  by_contra hDistinct
  let anchor : Sigma X := ⟨i,x⟩
  let output : Sigma X := ⟨j,y⟩
  let base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({anchor} : Finset (Sigma X))
  have hAnchor : anchor ∈ base.vertices := by
    simp [base,FiniteInduced.ofFinset]
  have hOutputNot : output ∉ base.vertices := by
    intro h
    have hEq : output = anchor := by
      simpa only [base,FiniteInduced.ofFinset, Finset.mem_singleton] using h
    exact hDistinct hEq.symm
  let F : Set (Sigma X) := {output}
  obtain ⟨other,hOrbit,hAvoid⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap
      base output hOutputNot F (Set.finite_singleton output)
  obtain ⟨g,hFix,hMoved⟩ := hOrbit
  have hFixAnchor : g • anchor = anchor :=
    (RealAction.mem_pointwiseStabilizer base.vertices g).mp hFix
      anchor hAnchor
  have hFixX : g • x = x := by
    simpa only [anchor,Sigma.smul_mk,Sigma.mk.injEq,
      heq_eq_eq,true_and] using hFixAnchor
  have hMovedR : R x (g • y) := by
    simpa only [hFixX] using hInvariant g x y hR
  have hEqY : y = g • y :=
    hFunctional x y (g • y) hR hMovedR
  have hFixOutput : g • output = output := by
    simp only [output,Sigma.smul_mk,hEqY.symm]
  have hOtherEq : other = output := hMoved.symm.trans hFixOutput
  exact hAvoid (by simpa only [F, Set.mem_singleton_iff] using hOtherEq)

/-- In one original named sort, an invariant TOTAL functional
relation is the literal REAL identity. Actual source SAP is used;
no quotient assumption or definability-to-invariance shortcut. -/
theorem original_SAP_total_invariant_function_same_sort_is_identity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (R : X i → X i → Prop)
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hSerial : ∀ x : X i, ∃ y : X i, R x y)
    (hFunctional : ∀ x y z : X i,
      R x y → R x z → y = z) :
    R = (fun x y : X i => x = y) := by
  funext x y
  apply propext
  constructor
  · intro hR
    have hTagged :=
      original_SAP_invariant_function_edge_is_identity
        S H sap R hInvariant hFunctional x y hR
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTagged
  · intro hEq
    subst y
    obtain ⟨z,hR⟩ := hSerial x
    have hTagged :=
      original_SAP_invariant_function_edge_is_identity
        S H sap R hInvariant hFunctional x z hR
    have hEqXZ : x = z := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTagged
    rwa [← hEqXZ] at hR

/-- Distinct ORIGINAL named sorts admit NO nonempty invariant
functional relation under original age SAP. This is about the
literal old real sorts, not distinct hidden quotient sorts. -/
theorem original_SAP_no_cross_sort_invariant_function
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (hNe : i ≠ j)
    (R : X i → X j → Prop)
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hFunctional : ∀ x : X i, ∀ y z : X j,
      R x y → R x z → y = z) :
    ¬ ∃ x : X i, ∃ y : X j, R x y := by
  rintro ⟨x,y,hR⟩
  exact hNe (congrArg Sigma.fst
    (original_SAP_invariant_function_edge_is_identity
      S H sap R hInvariant hFunctional x y hR))

/-- If the B040 canonical transport has target kernel contained in
actual real equality, R is functional on its target. Therefore EVERY
R-edge is literal identity on the original tagged real source.
In particular nonempty such transport cannot cross named old sorts.

This does NOT claim E=Id yet: the corresponding E noncollapse is
discharged separately using original seriality and the actual target
kernel formula. -/
theorem original_SAP_transport_target_identity_edges
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (E : QuotientTransport.InvEq G (X i))
    (R : QuotientTransport.Rel (X i) (X j))
    (T : QuotientTransport.Transport E R)
    (hTargetId : ∀ y z : X j, T.target y z → y = z) :
    ∀ x : X i, ∀ y : X j, R x y →
      (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  intro x y hR
  apply original_SAP_invariant_function_edge_is_identity
    S H sap R T.invariant
  · intro a b c hab hac
    apply hTargetId b c
    exact (T.target_iff b c).mpr
      ⟨a,a,hab,E.val.refl a,hac⟩
  · exact hR

/-- Source07 C24-C30 actual old SAP *no-real-collapse*:
a nontrivial original source E-class cannot transport along
a genuine B040 serial/coserial invariant R to an equality
target kernel. The target relation necessarily contains a
pair of DISTINCT real target points.

This is proved from real input/output SAP rigidity, not by
assuming quotient fibre nonidentity, extra quotient homogeneity,
SAP/CCO on the target quotient, or equality of foreign charts.
The nontrivial original E is given by an actual distinct E-pair
rather than an abstract nonempty relation. -/
theorem original_SAP_transport_preserves_nonidentity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (E : QuotientTransport.InvEq G (X i))
    (hNontrivial : ∃ x z : X i, E x z ∧ x ≠ z)
    (R : QuotientTransport.Rel (X i) (X j))
    (T : QuotientTransport.Transport E R) :
    ∃ y z : X j, T.target y z ∧ y ≠ z := by
  by_contra hNo
  have hId : ∀ y z : X j, T.target y z → y = z := by
    intro y z h
    by_contra hneq
    exact hNo ⟨y,z,h,hneq⟩
  have hRigid :=
    original_SAP_transport_target_identity_edges
      S H sap E R T hId
  obtain ⟨x,z,hExz,hxz⟩ := hNontrivial
  obtain ⟨y,hxy⟩ := T.serial x
  obtain ⟨w,hzw⟩ := T.serial z
  have hXY : (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ :=
    hRigid x y hxy
  have hZW : (⟨i,z⟩ : Sigma X) = ⟨j,w⟩ :=
    hRigid z w hzw
  have hYW : y = w := hId y w
    ((T.target_iff y w).mpr ⟨x,z,hxy,hExz,hzw⟩)
  have hTag : (⟨i,x⟩ : Sigma X) = ⟨i,z⟩ := by
    calc
      (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := hXY
      _ = ⟨j,w⟩ := congrArg (fun a : X j => (⟨j,a⟩ : Sigma X)) hYW
      _ = ⟨i,z⟩ := hZW.symm
  have hEq : x = z := by
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTag
  exact hxz hEq

end CCO.TransitionClosure
