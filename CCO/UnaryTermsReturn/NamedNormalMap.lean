import CCO.UnaryTermsReturn.RawIdentityClassification
import CCO.UnaryTermsReturn.NormalizedKernels

/-!
# B052 C10–C12 and QT-NF: every genuine RAW transition has a NAMED term

Suppose an ACTUAL old-G invariant nonempty RAW relation R is
quotient-functional over one genuinely represented proper original
coordinate K, with its actual B040 target the genuine named F.
Then the canonical quotient map is a literal finite term of the
B049 named hidden grammar. No arbitrary invariant relation is
declared a new primitive and no quotient-action sections are used.

If R contains any original identity pair, original transitivity
gives the real full diagonal, so the quotient map is the EXISTING
named identity. Otherwise the entire R is a valid identity-free
finite B049 RAW transition SYMBOL. Its real kernel bound follows
from the actual B040 T.kernel, and its target name is F by the
FULL original-G target equivalence and proof irrelevance.

This separates RAW equality from STRONG diversity and preserves
different original endpoint sorts.
-/

universe u v w t
namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- FULL source10 named transition alternative for any actual
NONEMPTY original RAW R satisfying a source kernel bound.
The target namedness F is not assumed abstractly: in the
intended receiver it is independently supplied by B049 old
SAP, actual original FULL MI and terminal FULL NR2.

Conclusion is a genuine source-term in the old finite named
signature, with the ACTUAL edge action at every R-pair. -/
theorem original_named_raw_transport_has_named_expression
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (K : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j)
    (T : Transport (originalColourEqAsInvEq S H K.val) R.val.val)
    (hF : originalTransportTargetColourEq S H K.val T = F.val) :
    ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 K F,
      ∀ (x : X i) (y : X j), R.val.val x y →
        OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
          (Quotient.mk K.val.val x) =
            Quotient.mk F.val.val y := by
  classical
  by_cases hDiagonal : ∃ x : X i, ∃ y : X j,
      R.val.val x y ∧ (⟨i,x⟩ : Sigma X) = ⟨j,y⟩
  · obtain ⟨x,y,hxy,hTag⟩ := hDiagonal
    have hij : i = j := congrArg Sigma.fst hTag
    cases hij
    have hxyEq : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTag
    subst y
    have hAll : ∀ z : X i, R.val.val z z :=
      original_raw_one_diagonal_implies_all S H R ⟨x,hxy⟩
    have hEqTarget : T.target =
        originalColourEqAsInvEq S H K.val :=
      original_identity_included_transport_target_eq_source T hAll
    have hFName : F = K := by
      apply Subtype.ext
      apply ColourEq.ext
      intro a b
      change F.val a b ↔ K.val a b
      rw [← hF]
      change T.target a b ↔ K.val a b
      rw [hEqTarget]
      exact Iff.rfl
    cases hFName
    refine ⟨.ident K, ?_⟩
    intro a b hab
    change (Quotient.mk K.val.val a) = Quotient.mk K.val.val b
    exact Quotient.sound
      (original_identity_included_transport_le_source T hAll a b hab)
  · have hNoIdentity : ∀ x : X i, ∀ y : X j,
        R.val.val x y → (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro x y hxy heq
      exact hDiagonal ⟨x,y,hxy,heq⟩
    let d : OriginalNamedRawTransitionSymbol S H i j :=
      ⟨⟨K,R⟩, by
        constructor
        · intro x z hxz
          obtain ⟨y,hxy,hzy⟩ := hxz
          exact T.kernel x z y hxy hzy
        · exact hNoIdentity⟩
    let Td := originalNamedRawTransitionSymbol_transport S H d
    have hTransport : Td = T := Subsingleton.elim _ _
    have hTargetInvEq : T.target =
        originalColourEqAsInvEq S H F.val := by
      rw [← hF]
      exact ((originalFullColourEqInvEqOrderIso S H).apply_symm_apply
        T.target).symm
    have hTargetName :
        originalNamedRawTransitionSymbol_target S H sap nr2 d = F := by
      apply Subtype.ext
      apply ColourEq.ext
      intro a b
      change Td.target a b ↔ F.val a b
      rw [hTransport,hTargetInvEq]
      exact Iff.rfl
    cases hTargetName
    refine ⟨.transition d (.ident K), ?_⟩
    intro x y hxy
    change Td.quotientEquiv (Quotient.mk K.val.val x) =
      Quotient.mk
        (originalNamedRawTransitionSymbol_target S H sap nr2 d).val.val y
    rw [hTransport]
    exact T.quotientEquiv_edge hxy

end CCO.UnaryTermsReturn
