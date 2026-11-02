import CCO.QuotientTransport.Composition

/-!
# B049 source07 C31-C34: identity-containing ORIGINAL RAW transports

The source's quotient transport relation R may contain true logical
identity together with real diversity edges. In the SAME original sort,
assuming actual RAW R;Rᵒᵖ ⊆ E, any such R is necessarily contained in E.
The actual transported kernel Rᵒᵖ;E;R is E itself, and the canonical
quotient bijection is the identity on genuine E-classes.

No positive-word identity letter is introduced, and the claims use
only the generic already ACCEPTED B040 kernel, not source SAP,
CCO, terminal representation, any quotient SAP or a chosen section.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

open CCO.QuotientTransport

/-- Original QT-Id C31: if R contains the true diagonal, the
literal B040 source kernel forces EVERY R-pair to be E-related.
In particular R need not equal the diagonal itself. -/
theorem original_identity_included_transport_le_source
    {E : InvEq G A} {R : Rel A A}
    (T : Transport E R) (hId : ∀ x : A, R x x) :
    ∀ x y : A, R x y → E x y := by
  intro x y hR
  exact T.kernel x y y hR (hId y)

/-- The full literal RAW R-converse ; E ; R target kernel is E
when R includes actual real logical identity. These are relations
on the true old carrier (not equality-deleted STRONG menus). -/
theorem original_identity_included_transport_raw_target
    {E : InvEq G A} {R : Rel A A}
    (T : Transport E R) (hId : ∀ x : A, R x x) :
    (fun x y : A => ∃ a b : A, R a x ∧ E a b ∧ R b y) = E.val.r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a,b,hAx,hAB,hBy⟩
    have hEaX : E a x :=
      original_identity_included_transport_le_source T hId a x hAx
    have hEbY : E b y :=
      original_identity_included_transport_le_source T hId b y hBy
    exact E.val.trans (E.val.symm hEaX)
      (E.val.trans hAB hEbY)
  · intro hE
    exact ⟨x,y,hId x,hE,hId y⟩

/-- Source original identity redundancy on the *actual* canonical
B040 transported full invariant target: its kernel is not a new
quotient coordinate. The proof uses the genuine target labels,
not a quotient-chart renaming assumption. -/
theorem original_identity_included_transport_target_eq_source
    {E : InvEq G A} {R : Rel A A}
    (T : Transport E R) (hId : ∀ x : A, R x x) :
    T.target = E := by
  apply InvEq.ext
  intro x y
  change T.label x = T.label y ↔ E x y
  rw [T.label_edge (hId x), T.label_edge (hId y)]
  exact Quotient.eq

/-- The actual canonical quotient E/R-target bijection is
POINTWISE identity after the preceding derived equality of the
target setoids. This does not assert R=Id as a real relation. -/
theorem original_identity_included_transport_quotient_eq_id
    {E : InvEq G A} {R : Rel A A}
    (T : Transport E R) (hId : ∀ x : A, R x x)
    (q : Quotient E.val) :
    InvEq.quotientCongr
        (original_identity_included_transport_target_eq_source T hId)
        (T.quotientEquiv q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      rw [T.quotientEquiv_edge (hId x),
        InvEq.quotientCongr_mk]

end CCO.TransitionClosure
