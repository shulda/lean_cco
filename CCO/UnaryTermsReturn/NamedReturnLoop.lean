import CCO.UnaryTermsReturn.NamedReturnFactors
import CCO.UnaryTermsReturn.TermComposition

/-!
# B052 C30–C36: literal named RAW return word, not only abstract holonomy

Each factor of a closed nonempty original-G invariant typed RAW word
has a B052 genuine NAMED B049 unary transition between the ACTUAL
represented proper FULL MI coordinates at the two adjacent prefixes.
The suffix induction composes the actual names; its evaluation is
the B040 canonical predecessor label at every old target point.

At the initial prefix, this gives a NAMED unary term D→D whose
semantic function is literally identity on every actual D-class.
No new hidden-age SAP/CCO, independent transport chart, STRONG
identity letter, arbitrary empty RAW factor or HN completion input
is used. The original old SAP and FULL NR2 are needed only when
the generic kernels are upgraded to named proper coordinates.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- At the actual complete-word prefix, the last typed old sort is
literally the starting original sort, and the named terminal FULL
kernel is EXACTLY the initial D (not just isomorphic). This works
for an arbitrary valid prefix/suffix B040 Bound with empty suffix;
a separately supplied initial Bound is not needed here. -/
theorem original_named_return_empty_suffix_coordinate_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a a)
    (h : Return.Bound
      (originalColourEqAsInvEq S H D.val) p (.nil a)) :
    originalNamedReturnPrefixCoordinate S H sap nr2
      D p (.nil a) h = D := by
  let E : InvEq G (X a) := originalColourEqAsInvEq S H D.val
  let trans := originalReturnSortTransitivity S H
  have hTarget : (Return.prefixTransport E trans p (.nil a) h).target = E :=
    Return.final_target E trans p h
  apply Subtype.ext
  apply ColourEq.ext
  intro x y
  change (Return.prefixTransport E trans p (.nil a) h).target x y ↔
    E x y
  rw [hTarget]

/-- The same target/source equality at the initial original prefix.
This keeps the entire actual closed RAW word as the suffix, so no
empty transition is manufactured. -/
theorem original_named_return_empty_prefix_coordinate_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (word : Word G X a a)
    (h : Return.Bound
      (originalColourEqAsInvEq S H D.val) (.nil a) word) :
    originalNamedReturnPrefixCoordinate S H sap nr2
      D (.nil a) word h = D := by
  let E : InvEq G (X a) := originalColourEqAsInvEq S H D.val
  let trans := originalReturnSortTransitivity S H
  have hTarget : (Return.prefixTransport E trans (.nil a) word h).target = E :=
    Return.initial_target E trans word h
  apply Subtype.ext
  apply ColourEq.ext
  intro x y
  change (Return.prefixTransport E trans (.nil a) word h).target x y ↔
    E x y
  rw [hTarget]

/-- Every suffix of ONE actual closed RAW word is represented by
a genuine finite NAMED composite from its current prefix coordinate
to the ORIGINAL initial named coordinate D.

More precisely, evaluation of this literal term at any old point's
current quotient class equals the B040 CANONICAL label of that
prefix. These labels are independent of any choice of quotient
section and compose with the same adjacent FULL kernels. -/
theorem original_named_return_suffix_literal_term
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a i : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i)
    (s : Word G X i a)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p s) :
    let K := originalNamedReturnPrefixCoordinate S H sap nr2 D p s h
    ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 K D,
      ∀ y : X i,
        OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
          (Quotient.mk K.val.val y) =
        (Return.prefixTransport
          (originalColourEqAsInvEq S H D.val)
          (originalReturnSortTransitivity S H)
          p s h).label y := by
  induction s with
  | nil a =>
      have hK : originalNamedReturnPrefixCoordinate
          S H sap nr2 D p (.nil a) h = D :=
        original_named_return_empty_suffix_coordinate_eq
          S H sap nr2 D p h
      rw [hK]
      refine ⟨.ident D, ?_⟩
      intro y
      change Quotient.mk D.val.val y =
        (Return.prefixTransport
          (originalColourEqAsInvEq S H D.val)
          (originalReturnSortTransitivity S H)
          p (.nil a) h).label y
      exact (Return.final_label
        (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H) p h y).symm
  | @cons i j a P tail ih =>
      let E : InvEq G (X a) :=
        originalColourEqAsInvEq S H D.val
      let trans := originalReturnSortTransitivity S H
      let hn : Return.Bound E (p.extend P) tail :=
        Return.next_bound E p P tail h
      obtain ⟨theta0,hEdge,_⟩ :=
        original_named_return_factor_term
          S H sap nr2 D p P tail h
      obtain ⟨theta1,hSuffix⟩ := ih D (p.extend P) hn
      refine ⟨originalNamedRawUnaryTerm_prepend
          S H sap nr2 theta0 theta1, ?_⟩
      intro y
      obtain ⟨z,hyz⟩ :=
        (serial_coserial_of_invariant
          P.relation P.invariant P.nonempty
          (trans i) (trans j)).1 y
      calc
        OriginalNamedRawUnaryTerm.eval S H sap nr2
          (originalNamedRawUnaryTerm_prepend
            S H sap nr2 theta0 theta1)
          (Quotient.mk
            (originalNamedReturnPrefixCoordinate
              S H sap nr2 D p (.cons P tail) h).val.val y) =
            OriginalNamedRawUnaryTerm.eval S H sap nr2 theta1
              (OriginalNamedRawUnaryTerm.eval S H sap nr2 theta0
                (Quotient.mk
                  (originalNamedReturnPrefixCoordinate
                    S H sap nr2 D p (.cons P tail) h).val.val y)) :=
              originalNamedRawUnaryTerm_prepend_eval
                S H sap nr2 theta0 theta1 _
        _ = OriginalNamedRawUnaryTerm.eval S H sap nr2 theta1
            (Quotient.mk
              (originalNamedReturnPrefixCoordinate S H sap nr2
                D (p.extend P) tail hn).val.val z) := by
              rw [hEdge y z hyz]
        _ = (Return.prefixTransport E trans (p.extend P) tail hn).label z :=
              hSuffix z
        _ = (Return.prefixTransport E trans p (.cons P tail) h).label y :=
          (Return.edge_label E trans p P tail h hyz).symm

/-- FULL source10 named-loop conclusion: there is an ACTUAL B049
named syntax word on the original terminal represented coordinate
D whose semantic value on ALL D-classes is literally the identity.

The word comes from the exact nonempty original-G RAW factors of
the supplied closed word. This is stronger than merely using B040
abstract quotient holonomy in the conclusion. -/
theorem original_named_raw_closed_word_has_identity_term
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (word : Word G X a a)
    (hWord : Return.Bound
      (originalColourEqAsInvEq S H D.val) (.nil a) word) :
    ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 D D,
      OriginalNamedRawUnaryTerm.eval S H sap nr2 theta = id := by
  have hK : originalNamedReturnPrefixCoordinate S H sap nr2
      D (.nil a) word hWord = D :=
    original_named_return_empty_prefix_coordinate_eq
      S H sap nr2 D word hWord
  have hSuffix := original_named_return_suffix_literal_term
    S H sap nr2 D (.nil a) word hWord
  rw [hK] at hSuffix
  obtain ⟨theta,hTheta⟩ := hSuffix
  refine ⟨theta, ?_⟩
  funext q
  induction q using Quotient.inductionOn with
  | _ y =>
      change OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
        (Quotient.mk D.val.val y) = Quotient.mk D.val.val y
      rw [hTheta y]
      exact Return.initial_label
        (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H)
        word hWord y

end CCO.UnaryTermsReturn
