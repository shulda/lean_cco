import CCO.UnaryTermsReturn.RootSignatureBundle
import CCO.TransitionClosure.OriginalNamedRawUnaryLanguage

/-!
# B052 D06/C05: actual complete theta-bundle root signature

An old typed actual guarded constraint D is the intersection of
a finite family of true invariant RAW branch profiles P_k.
For every genuinely represented proper FULL source quotient
coordinate J on which D is quotient-functional, and independently
for every represented J on which EACH P_k is quotient-functional,
keep the literal B040 named transition equation. The complete
family is constructed, not chosen or assumed consistent.

All displayed equations and EVERY named unary continuation are
valid at the ACTUAL real root pair satisfying D. The construction
uses the original homogeneous G, visible old SAP and original FULL
NR2. No hidden SAP/homogeneity, unrelated quotient chart, identity
STRONG atom or arbitrary partial-source completion is asserted.
-/

universe u v w t q

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- One ORIGINAL actual named source kernel J for which the
given genuine old invariant RAW relation is quotient-functional.
This does not claim J is automatically named from an arbitrary
invariant relation: proper representedness is literal data. -/
abbrev OriginalRootFunctionalProfile
    (H : HomogeneousSource S G) {i j : ι}
    (R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j) :=
  {J : OriginalNamedHiddenCoordinate S H i //
    ∀ a c : X i,
      QuotientTransport.compose R.val.val
        (QuotientTransport.converse R.val.val) a c →
        J.val a c}

/-- The B040 canonical quotient action for an ACTUAL original
invariant relation, with seriality/coseriality obtained from
old source transitivity and the given genuine nonempty edge
family. The named target comes only from old SAP and FULL NR2. -/
noncomputable def originalRootEquationDatumOfProfile
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j)
    (R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j)
    (hxy : R.val.val x y)
    (J : OriginalRootFunctionalProfile S H R) :
    OriginalActualRootEquationDatum S H x y :=
  { J := J.val
    R := R.val.val
    T := typed_quotient_transport
      (originalColourEqAsInvEq S H J.val.val)
      R.val.val R.val.property R.property
      (S.original_sort_transitive_of_homogeneous H i)
      (S.original_sort_transitive_of_homogeneous H j)
      J.property
    edge := hxy }

/-- A REAL original theta intersection D=intersection P_k.
The equality is over the whole old typed pair carrier, not
only at the displayed roots; the given root pair satisfies D.
Every branch is a true old G-invariant NONEMPTY RAW relation,
not a separately invented hidden binary predicate. -/
structure OriginalActualThetaRootData
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) (I : Type q) where
  direct : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j
  branch : I → OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j
  intersection : ∀ a : X i, ∀ b : X j,
    direct.val.val a b ↔ ∀ k : I, (branch k).val.val a b
  edge : direct.val.val x y

/-- EVERY direct and branch-forced functional source coordinate,
as a SET of genuine named root-transition data. The index over
represented kernels is NOT truncated, and different kernels
are kept distinct. No independent target chart is chosen. -/
noncomputable def originalActualThetaRootSignature
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) {I : Type q}
    (theta : OriginalActualThetaRootData S H x y I) :
    Set (OriginalActualRootEquationDatum S H x y) :=
  Set.range (fun J : OriginalRootFunctionalProfile S H theta.direct =>
    originalRootEquationDatumOfProfile S H x y theta.direct theta.edge J) ∪
  (⋃ k : I, Set.range
    (fun J : OriginalRootFunctionalProfile S H (theta.branch k) =>
      originalRootEquationDatumOfProfile S H x y
        (theta.branch k)
        ((theta.intersection x y).mp theta.edge k) J))

/-- The signature contains the direct D transition equation for
EVERY represented proper FULL J with DD^op <= J. -/
theorem original_actual_theta_root_direct_included
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) {I : Type q}
    (theta : OriginalActualThetaRootData S H x y I)
    (J : OriginalRootFunctionalProfile S H theta.direct) :
    originalRootEquationDatumOfProfile
        S H x y theta.direct theta.edge J ∈
      originalActualThetaRootSignature S H x y theta := by
  exact Or.inl ⟨J,rfl⟩

/-- For EVERY actual theta branch k, the signature contains
ALL functional equations at the represented proper source
kernels of that branch. No branch is silently discarded. -/
theorem original_actual_theta_root_branch_included
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) {I : Type q}
    (theta : OriginalActualThetaRootData S H x y I)
    (k : I) (J : OriginalRootFunctionalProfile S H (theta.branch k)) :
    originalRootEquationDatumOfProfile
        S H x y (theta.branch k)
        ((theta.intersection x y).mp theta.edge k) J ∈
      originalActualThetaRootSignature S H x y theta := by
  exact Or.inr (Set.mem_iUnion.mpr ⟨k,⟨J,rfl⟩⟩)

/-- Every direct AND every forced branch equation in the whole
source10 theta signature holds simultaneously at the actual
root pair. This consumes only genuine original quotient actions. -/
theorem original_actual_theta_root_all_equations
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i) (y : X j) {I : Type q}
    (theta : OriginalActualThetaRootData S H x y I) :
    ∀ d ∈ originalActualThetaRootSignature S H x y theta,
      OriginalActualRootEquation S H sap nr2 d := by
  exact original_actual_root_bundle_consistent
    S H sap nr2 x y (originalActualThetaRootSignature S H x y theta)

/-- The FULL functional closure of the constructed source10
theta bundle: any genuine named term on any actual transported
target preserves each direct or branch equation, including
arbitrarily long terms and upward maps. -/
theorem original_actual_theta_root_all_named_continuations
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i) (y : X j) {I : Type q}
    (theta : OriginalActualThetaRootData S H x y I) :
    ∀ d ∈ originalActualThetaRootSignature S H x y theta,
      ∀ {k : ι}
        (F : OriginalNamedHiddenCoordinate S H k)
        (word : OriginalNamedRawUnaryTerm S H sap nr2
          (originalRootNamedTarget S H sap nr2 d.J d.T) F),
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (d.T.quotientEquiv (Quotient.mk d.J.val.val x)) =
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (Quotient.mk
            (originalRootNamedTarget S H sap nr2 d.J d.T).val.val y) := by
  exact original_actual_root_bundle_all_named_continuations
    S H sap nr2 x y (originalActualThetaRootSignature S H x y theta)

end CCO.UnaryTermsReturn
