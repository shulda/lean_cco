import CCO.UnaryTermsReturn.NamedIntermediate
import CCO.UnaryTermsReturn.NamedNormalMap

/-!
# B052 C30/C34–C36: named REAL typed RAW return factors

B040 Return constructs the true canonical prefix transport and
the true factor transport for an arbitrary closed nonempty
original-G invariant RAW word. Its exact factor_target theorem
identifies the target FULL kernel of each factor with the
source FULL kernel of the next prefix.

B052 previously upgraded each prefix to a genuinely named
proper FULL original hidden coordinate using old SAP and FULL
NR2. Here every adjacent original RAW factor receives an
ACTUAL named B049 unary term between precisely those two
coordinates. A diagonal-containing factor uses the already
named identity, not a fictitious STRONG identity atom.

This does NOT merely select unrelated quotient charts; each
source/target equivalence is proved equal to the canonical
B040 prefix/factor kernel using literal relational witnesses.
No hidden SAP/CCO or new source condition is invoked.
-/

universe u v w t
namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- Every canonical RAW LETTER of a genuine typed closed
word is an actual nonempty invariant original-G relation,
not an arbitrary new primitive or a possibly empty factor. -/
def originalNamedReturnLetterAsOldRaw
    {i j : ι} (P : Letter G X i j) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j :=
  ⟨⟨P.relation,P.invariant⟩,P.nonempty⟩

/-- B052 named factor lemma. The source K0 and target K1
are the ACTUAL named B040 prefix kernel coordinates. Every
edge y P z is realized by a genuine already-named unary
transition term theta:K0→K1, not by an arbitrary chosen
equivalence between their quotient carriers.

The factors and the intermediate kernels come from ONE
closed RAW word and its ONE original quotient D. The
nonempty-letter condition is structural. -/
theorem original_named_return_factor_term
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a i j : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i)
    (P : Letter G X i j)
    (s : Word G X j a)
    (hWord : Return.Bound
      (originalColourEqAsInvEq S H D.val)
        p (.cons P s)) :
    let K0 := originalNamedReturnPrefixCoordinate
      S H sap nr2 D p (.cons P s) hWord
    let K1 := originalNamedReturnPrefixCoordinate
      S H sap nr2 D (p.extend P) s
        (Return.next_bound
          (originalColourEqAsInvEq S H D.val) p P s hWord)
    ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 K0 K1,
      (∀ (y : X i) (z : X j), P.relation y z →
        OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
          (Quotient.mk K0.val.val y) =
          Quotient.mk K1.val.val z) ∧
      Function.Injective
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 theta) := by
  let E : InvEq G (X a) := originalColourEqAsInvEq S H D.val
  let trans := originalReturnSortTransitivity S H
  let pre := Return.prefixTransport E trans p (.cons P s) hWord
  let after := Return.prefixTransport E trans (p.extend P) s
    (Return.next_bound E p P s hWord)
  let U := Return.factor E trans p P s hWord
  let K0 := originalNamedReturnPrefixCoordinate
    S H sap nr2 D p (.cons P s) hWord
  let K1 := originalNamedReturnPrefixCoordinate
    S H sap nr2 D (p.extend P) s
      (Return.next_bound E p P s hWord)
  have h0 :
      originalColourEqAsInvEq S H K0.val = pre.target := by
    have hK := originalNamedReturnPrefixCoordinate_kernel
      S H sap nr2 D p (.cons P s) hWord
    rw [hK]
    exact (originalFullColourEqInvEqOrderIso S H).apply_symm_apply pre.target
  have h1 :
      originalColourEqAsInvEq S H K1.val = after.target := by
    have hK := originalNamedReturnPrefixCoordinate_kernel
      S H sap nr2 D (p.extend P) s
        (Return.next_bound E p P s hWord)
    rw [hK]
    exact (originalFullColourEqInvEqOrderIso S H).apply_symm_apply after.target
  let R := originalNamedReturnLetterAsOldRaw (X := X) (G := G) P
  have T : Transport
      (originalColourEqAsInvEq S H K0.val) R.val.val := by
    rw [h0]
    exact U
  have hTU : T.target = U.target := by
    apply InvEq.ext
    intro y z
    rw [T.target_iff,U.target_iff]
    change (∃ x x', P.relation x y ∧
      (originalColourEqAsInvEq S H K0.val) x x' ∧ P.relation x' z) ↔
      (∃ x x', P.relation x y ∧ pre.target x x' ∧ P.relation x' z)
    rw [h0]
  have hF : originalTransportTargetColourEq S H K0.val T = K1.val := by
    apply ColourEq.ext
    intro y z
    change T.target y z ↔ K1.val y z
    rw [hTU, Return.factor_target E trans p P s hWord]
    change after.target y z ↔
      (originalColourEqAsInvEq S H K1.val) y z
    rw [h1]
  exact original_named_raw_transport_has_named_expression
    S H sap nr2 K0 K1 R T hF

end CCO.UnaryTermsReturn
