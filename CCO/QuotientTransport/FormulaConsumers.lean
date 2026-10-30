import CCO.QuotientTransport.Consumers
import CCO.QuotientTransport.Definability

/-! The separate first-order gate is attached to the actual constructed
kernels. Generic core and return files do not import this formula layer. -/
universe u v w z
namespace CCO.QuotientTransport
open Definability
variable {I : Type u} {X : I → Type v} {G : Type z} [Group G]
variable [∀ i, MulAction G (X i)]

theorem Transport.target_relation {i j : I} {E : InvEq G (X i)} {R : TRel X i j}
    (T : Transport E R) :
    T.target.val.r = TRel.comp (TRel.converse R) (TRel.comp E.val.r R) := by
  funext y z
  apply propext
  rw [T.target_iff]
  constructor
  · rintro ⟨x,x',hr,he,hr'⟩
    exact ⟨x,hr,x',he,hr'⟩
  · rintro ⟨x,hr,x',he,hr'⟩
    exact ⟨x,x',hr,he,hr'⟩

/-- Arbitrary ambient first-order language: only actual input formulas are
required, and the resulting actual kernel has the displayed existential one. -/
theorem Transport.target_has_formula {i j : I} {E : InvEq G (X i)} {R : TRel X i j}
    (T : Transport E R) {L : FirstOrder.Language} [L.Structure (Sigma X)]
    (hR : TypedHasFormula (L := L) R) (hE : TypedHasFormula (L := L) E.val.r) :
    TypedHasFormula (L := L) T.target.val.r := by
  rw [T.target_relation]
  exact typed_transport_has_formula hR hE

variable (S : AtomicSource.{u,v,w} I X) (H : HomogeneousSource S G)
include H

/-- C13/C14: the intended finite named orbital source discharges BOTH
input-formula gates, and the result is the actual constructed equivalence. -/
theorem Transport.source_target_has_formula {i j : I} {E : InvEq G (X i)} {R : TRel X i j}
    (T : Transport E R) : TypedHasFormula (L := namedLanguage S) T.target.val.r :=
  T.target_has_formula (source_invariant_has_formula S H R T.invariant)
    (source_invariant_has_formula S H E.val.r E.property)

variable {a : I} (E : InvEq G (X a))
variable (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y)

/-- C25/C26: actual original finite formulas at EVERY cut, simultaneously
for EVERY invariant coarsening. No generic invariance-to-definability rule
is asserted: S,H and their proved finite orbital formulas are used here. -/
theorem source_return_every_coarsening {i : I} (p : Word G X a i) (s : Word G X i a)
    (h : Return.Bound E p s) (J : InvEq G (X a)) (hEJ : E ≤ J) :
    TypedHasFormula (L := namedLanguage S)
      (Return.prefixTransport J trans p s (Return.coarser_bound E hEJ p s h)).target.val.r := by
  apply Transport.target_has_formula
  · exact source_typedWord_has_formula S H Letter.relation (fun _ _ P => P.invariant) p
  · exact source_invariant_has_formula S H J.val.r J.property

/-- The canonical label coarsening and its formula are proved together in the
intended source, retaining the actual canonical map a/E→a/J. -/
theorem source_coarsening_consumer {i : I} (p : Word G X a i) (s : Word G X i a)
    (h : Return.Bound E p s) (J : InvEq G (X a)) (hEJ : E ≤ J) :
    (∀ y, (Return.prefixTransport J trans p s (Return.coarser_bound E hEJ p s h)).label y =
      Quot.mapRight hEJ ((Return.prefixTransport E trans p s h).label y)) ∧
      TypedHasFormula (L := namedLanguage S)
        (Return.prefixTransport J trans p s (Return.coarser_bound E hEJ p s h)).target.val.r :=
  ⟨Return.coarser_label E trans hEJ p s h,source_return_every_coarsening S H E trans p s h J hEJ⟩
end CCO.QuotientTransport
