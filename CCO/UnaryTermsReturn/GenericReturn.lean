import CCO.QuotientTransport.Return
import CCO.TransitionClosure.OriginalNamedHiddenCoordinates

/-!
# B052 C28–C36 — actual canonical generic RAW return holonomy

The foundational B040 Return construction already formalizes the
NONEMPTY, G-invariant, typed RAW letters, their serial/coseriality,
literal prefix and factor kernels, and canonical quotient labels.

We expose the precise generic return on the SAME literal carrier,
and simultaneously all coarser FULL invariant kernels. This uses
only a transitive group action on each original nonempty carrier,
not original SAP, CCO, terminal NR2, a faithful action or arbitrary
quotient reduct homogeneity.

For the ACTUAL original source, terminal FULL NR2 separately
provides the named source proper FULL MI coordinate. The stronger
claim that EVERY intermediate transported kernel is again a named
proper coordinate is a further B052 obligation, not asserted here.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.QuotientTransport
open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Source10's GENERIC canonical holonomy, explicitly bound by
a nonempty invariant typed RAW word and its LITERAL equality-
inclusive product relation. The previous B040 provider proves
all prefix source-kernel obligations rather than hypothesizing
individual unrelated quotient charts. Empty letters are excluded
by the genuine Letter.nonempty field. -/
theorem generic_typed_raw_return_identity
    {a : ι} (E : InvEq G (X a))
    (trans : ∀ i : ι, ∀ x y : X i, ∃ g : G, g • x = y)
    (word : Word G X a a)
    (hWord : Return.Bound E (.nil a) word) :
    Return.holonomy E trans word hWord = id :=
  Return.holonomy_identity E trans word hWord

/-- Uniformity at ALL coarser invariant kernels J >= E,
with exactly the SAME sequence of original RAW letters.
No transport exactness/naming and no hidden SAP are assumed. -/
theorem generic_typed_raw_return_all_coarsenings
    {a : ι} (E : InvEq G (X a))
    (trans : ∀ i : ι, ∀ x y : X i, ∃ g : G, g • x = y)
    (word : Word G X a a)
    (hWord : Return.Bound E (.nil a) word)
    (J : InvEq G (X a)) (hEJ : E ≤ J) :
    Return.holonomy J trans word
      (Return.coarser_bound E hEJ (.nil a) word hWord) = id :=
  Return.all_coarser_holonomy E trans word hWord J hEJ

/-- Each ACTUAL adjacent typed factor has the SAME target
kernel as the next canonical prefix transport; this is the
essential seam equality and not an arbitrary chart choice. -/
theorem generic_typed_raw_factor_target
    {a i j : ι} (E : InvEq G (X a))
    (trans : ∀ k : ι, ∀ x y : X k, ∃ g : G, g • x = y)
    (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a)
    (hWord : Return.Bound E p (.cons P s)) :
    (Return.factor E trans p P s hWord).target =
      (Return.prefixTransport E trans (p.extend P) s
        (Return.next_bound E p P s hWord)).target :=
  Return.factor_target E trans p P s hWord

/-- The source-mapped prefix/factor maps commute with
EVERY coarsening under literal class projections: no
ad hoc quotient section can be inserted between steps. -/
theorem generic_typed_raw_coarser_factor_step
    {a i j : ι} (E J : InvEq G (X a))
    (hEJ : E ≤ J)
    (trans : ∀ k : ι, ∀ x y : X k, ∃ g : G, g • x = y)
    (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a)
    (hWord : Return.Bound E p (.cons P s))
    (q : Quotient (Return.prefixTransport E trans p
      (.cons P s) hWord).target.val) :
    Return.step J trans p P s
      (Return.coarser_bound E hEJ p (.cons P s) hWord)
      (Quot.mapRight
        (Return.coarser_kernel E trans hEJ p
          (.cons P s) hWord) q) =
      Quot.mapRight
        (Return.coarser_kernel E trans hEJ (p.extend P) s
          (Return.next_bound E p P s hWord))
        (Return.step E trans p P s hWord q) :=
  Return.coarser_step E trans hEJ p P s hWord q

variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Actual ORIGINAL full-G source instance of the generic
closed-RAW theorem. The homogeneity here supplies actual sort
transitivity and invariant FULL old kernels; neither SAP/CCO
nor terminal NR2 is used for the generic return identity. -/
theorem original_full_equivalence_raw_return_identity
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (word : Word G X i i)
    (hWord : Return.Bound (originalColourEqAsInvEq S H J)
      (.nil i) word) :
    Return.holonomy
      (originalColourEqAsInvEq S H J)
      (fun k x y => S.original_sort_transitive_of_homogeneous H k x y)
      word hWord = id :=
  generic_typed_raw_return_identity
    (originalColourEqAsInvEq S H J)
    (fun k x y => S.original_sort_transitive_of_homogeneous H k x y)
    word hWord

/-- Source10 named FIRST coordinate instance: for a FULL
original proper MI J > Id, terminal FULL NR2 constructs one
ACTUAL represented named hidden coordinate D with D.val = J.
The generic loop returns to the same underlying original
J-quotient; any intermediate represented naming remains a
separate (not silently imported) source10 obligation. -/
theorem original_named_starting_coordinate_return
    (H : HomogeneousSource S G)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJMI : ProperMeetIrreducible
      (originalColourEqAsInvEq S H J))
    (word : Word G X i i)
    (hWord : Return.Bound (originalColourEqAsInvEq S H J)
      (.nil i) word) :
    ∃ D : OriginalNamedHiddenCoordinate S H i,
      D.val = J ∧
      Return.holonomy
        (originalColourEqAsInvEq S H J)
        (fun k x y => S.original_sort_transitive_of_homogeneous H k x y)
        word hWord = id := by
  refine ⟨original_full_MI_named_hidden_of_terminalNR2
    S H nr2 J hJbot hJMI, rfl, ?_⟩
  exact original_full_equivalence_raw_return_identity S H J word hWord

end CCO.UnaryTermsReturn
