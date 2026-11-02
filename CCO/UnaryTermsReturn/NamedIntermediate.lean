import CCO.UnaryTermsReturn.GenericReturn

/-!
# B052 C34 — genuinely NAMED coordinates at all RAW return prefixes

The accepted B040 generic return builds all prefix quotient transports
with their ACTUAL invariant source/target kernels. In the TERMINAL
original homogeneous source, B049's OLD SAP noncollapse and original
FULL NR2 RAW naming upgrade those invariant transported proper
meet-irreducibles to existing represented hidden coordinates.

This does not infer hidden homogeneity/SAP or replace the actual
return's common intermediate kernel by a separately chosen chart.
Each named coordinate is a subtype of the true original ColourEq.
The individual named primitive factors are a later obligation.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.QuotientTransport
open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Actual original group transitivity on EVERY old typed sort,
not an assumed group action on the hidden quotient age. -/
def originalReturnSortTransitivity
    (H : HomogeneousSource S G) :
    ∀ i : ι, ∀ x y : X i, ∃ g : G, g • x = y :=
  fun i x y => S.original_sort_transitive_of_homogeneous H i x y

/-- Each genuine prefix of a closed original RAW word starting
at a represented proper FULL MI D has an ACTUAL named proper
FULL MI target. Generic B040 transport supplies its literal
kernel; original SAP prevents an equality target and full
NR2 independently supplies one genuine original RAW name.
No quotient SAP/CCO, new source equivalence or section. -/
noncomputable def originalNamedReturnPrefixCoordinate
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a i : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i) (s : Word G X i a)
    (hWord : Return.Bound
      (originalColourEqAsInvEq S H D.val) p s) :
    OriginalNamedHiddenCoordinate S H i :=
  original_named_hidden_transport_target S H sap nr2 D
    (Return.prefixTransport
      (originalColourEqAsInvEq S H D.val)
      (originalReturnSortTransitivity S H)
      p s hWord)

/-- The actual named intermediate target retains the EXACT
B040 prefix target kernel, not merely an abstract isomorphic
quotient coordinate; FULL raw representability is separately
discharged by the terminal no-index-two theorem. -/
theorem originalNamedReturnPrefixCoordinate_kernel
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a i : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i) (s : Word G X i a)
    (hWord : Return.Bound
      (originalColourEqAsInvEq S H D.val) p s) :
    (originalNamedReturnPrefixCoordinate
      S H sap nr2 D p s hWord).val =
      originalTransportTargetColourEq S H D.val
        (Return.prefixTransport
          (originalColourEqAsInvEq S H D.val)
          (originalReturnSortTransitivity S H)
          p s hWord) := rfl

/-- At the literal FINAL original sort the named transported
quotient kernel is not just equivalent to the source coordinate:
it is the SAME original FULL equivalence D, and hence the SAME
named hidden coordinate object by proof irrelevance.
This uses B040 Return.final_target and the true old-G full
ColourEq/InvEq identification. -/
theorem originalNamedReturnFinalCoordinate_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (word : Word G X a a)
    (hWord : Return.Bound
      (originalColourEqAsInvEq S H D.val) (.nil a) word) :
    originalNamedReturnPrefixCoordinate S H sap nr2
      D word (.nil a) hWord = D := by
  let E : InvEq G (X a) := originalColourEqAsInvEq S H D.val
  let trans := originalReturnSortTransitivity S H
  let T := Return.prefixTransport E trans word (.nil a) hWord
  have hTarget : T.target = E :=
    Return.final_target E trans word hWord
  apply Subtype.ext
  apply ColourEq.ext
  intro x y
  change T.target x y ↔ E x y
  rw [hTarget]

/-- Prefix naming is compatible with any coarser INITIAL
represented source J of an arbitrary generic E0 <= J, by
the SAME actual closed word: B040 derives its coarser
prefix kernel. This constructs an actual named coordinate
at each position, not an ad hoc chart. -/
noncomputable def originalNamedCoarserReturnPrefixCoordinate
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {a i : ι} (E0 : InvEq G (X a))
    (D : OriginalNamedHiddenCoordinate S H a)
    (hEJ : E0 ≤ originalColourEqAsInvEq S H D.val)
    (p : Word G X a i) (s : Word G X i a)
    (hWord : Return.Bound E0 p s) :
    OriginalNamedHiddenCoordinate S H i :=
  originalNamedReturnPrefixCoordinate S H sap nr2 D p s
    (Return.coarser_bound E0 hEJ p s hWord)

end CCO.UnaryTermsReturn
