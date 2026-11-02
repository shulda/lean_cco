import CCO.TransitionClosure.OriginalTransportProper
import CCO.QuotientTransport.Composition

/-!
# B049 source07 C35: literal canonical quotient/upward-map rewrite (TQU)

A B040 original typed RAW transport R:a→b gives a canonical
quotient bijection q_R:a/E→b/F with F=Rᵒᵖ;E;R.
For ANY original-G invariant target equivalence L≥F, its
FULL upper-interval inverse H0=pull_R(L)≥E is used, not
an independently chosen source quotient chart.

This file shows pointwise that upward b/F→b/L after q_R
equals canonical q_(R,H0) after upward a/E→a/H0.
Both send the literal E-class of any original point x to
the same L-class of an actual R-successor y.

No old SAP, quotient SAP, CCO, NR2, distributivity, hidden
coordinate or quotient-reduct automorphism group is needed
for this generic RAW equality; naming H0 as represented
under TERMINAL FULL NR2 remains a separate gate.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {G : Type t} [Group G]
variable {A : Type v} {B : Type w} [MulAction G A] [MulAction G B]

open CCO.QuotientTransport

/-- TQU for a chosen full source coarsening H≥E:
upward on the transported target is the SAME function as
transport after upstream coarsening. The transported
target really is T.push H h, and the upper map uses
the proved inclusion T.target≤T.push H h. -/
theorem original_transport_upward_naturality
    {E : InvEq G A} {R : Rel A B}
    (T : Transport E R)
    (H : InvEq G A) (hEH : E ≤ H)
    (q : Quotient E.val) :
    Quot.mapRight (T.target_le_push H hEH) (T.quotientEquiv q) =
      (T.enlarge hEH).quotientEquiv (Quot.mapRight hEH q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨y,hxy⟩ := T.serial x
      rw [T.quotientEquiv_edge hxy]
      change (Quotient.mk'' y : Quotient (T.push H hEH).val) =
        (T.enlarge hEH).quotientEquiv (Quotient.mk'' x)
      exact ((T.enlarge hEH).quotientEquiv_edge hxy).symm

/-- Source07 exact TQU with the FULL invariant source-side
inverse H0=pull_R(L) to any literal L≥F. The RHS is converted
by the proved E^(R,H0)=L equality, never by an unrelated
quotient isomorphism. This is equality of real unary FUNCTIONS,
not merely equality of words/nominal quotient labels. -/
theorem original_transport_upward_pull_rewrite
    {E : InvEq G A} {R : Rel A B}
    (T : Transport E R)
    (L : InvEq G B) (hFL : T.target ≤ L)
    (q : Quotient E.val) :
    Quot.mapRight hFL (T.quotientEquiv q) =
      InvEq.quotientCongr (T.push_pull L hFL)
        ((T.enlarge (T.source_le_pull L hFL)).quotientEquiv
          (Quot.mapRight (T.source_le_pull L hFL) q)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨y,hxy⟩ := T.serial x
      rw [T.quotientEquiv_edge hxy]
      change (Quotient.mk'' y : Quotient L.val) =
        InvEq.quotientCongr (T.push_pull L hFL)
          ((T.enlarge (T.source_le_pull L hFL)).quotientEquiv
            (Quotient.mk'' x))
      rw [(T.enlarge (T.source_le_pull L hFL)).quotientEquiv_edge hxy]
      exact (InvEq.quotientCongr_mk (T.push_pull L hFL) y).symm

end CCO.TransitionClosure
