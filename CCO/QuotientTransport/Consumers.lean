import CCO.QuotientTransport.Return
import CCO.QuotientTransport.Irreducible
import CCO.QuotientTransport.SharedActions.Boundaries
import CCO.QuotientTransport.Boundaries.NonDefinability
import CCO.QuotientTransport.Boundaries.Transport

/-! Receiving exports with the actual original action hypotheses. The two
action exports continue to consume B001's unchanged shared implementation.
Definability is deliberately a separate source-context result. -/
universe u v w z
namespace CCO.QuotientTransport
variable {G : Type u} [Group G] {A : Type v} {B : Type w}
variable [MulAction G A] [MulAction G B]

/-- `lem:typed-quotient-transport`: construction from exactly the generic
action hypotheses. All canonical labels, actual quotient bijections and the
full invariant interval are obtained by the preceding proved API. -/
theorem typed_quotient_transport (E : InvEq G A) (R : Rel A B)
    (invariant : Invariant (G := G) R) (nonempty : ∃ x y, R x y)
    (transA : ∀ x y : A, ∃ g : G, g • x = y)
    (transB : ∀ x y : B, ∃ g : G, g • x = y)
    (kernel : ∀ x x', compose R (converse R) x x' → E x x') : Transport E R := by
  obtain ⟨hs,hc⟩ := serial_coserial_of_invariant R invariant nonempty transA transB
  exact ⟨hs,hc,invariant,fun x x' y hx hx' => kernel x x' ⟨y,hx,hx'⟩⟩

/-- A real consumer of the complete kernel/label/quotient/interval DAG,
without a completion, exactness or definability callback. -/
theorem actual_transport_consumer (E : InvEq G A) (R : Rel A B)
    (invariant : Invariant (G := G) R) (nonempty : ∃ x y, R x y)
    (transA : ∀ x y : A, ∃ g : G, g • x = y)
    (transB : ∀ x y : B, ∃ g : G, g • x = y)
    (kernel : ∀ x x', compose R (converse R) x x' → E x x') :
    ∃ (F : InvEq G B) (label : B → Quotient E.val),
      Function.Surjective label ∧
      (∀ g y, label (g • y) = E.act g (label y)) ∧
      (∀ x y, R x y → label y = Quotient.mk'' x) ∧
      (∀ y z, F y z ↔ ∃ x x', R x y ∧ E x x' ∧ R x' z) ∧
      Nonempty (Quotient E.val ≃ Quotient F.val) ∧
      Nonempty ({H : InvEq G A // E ≤ H} ≃o {L : InvEq G B // F ≤ L}) := by
  let T := typed_quotient_transport E R invariant nonempty transA transB kernel
  exact ⟨T.target,T.label,T.label_surjective,T.label_equivariant,
    fun _ _ h => T.label_edge h,T.target_iff,⟨T.quotientEquiv⟩,⟨T.intervalIso⟩⟩

section ReturnConsumer
variable {I : Type z} {X : I → Type v} [∀ i, MulAction G (X i)]
variable {a : I} (E : InvEq G (X a))
variable (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y)

theorem whole_bound (s : Word G X a a) (h : ∀ x y, s.eval x y → E x y) :
    Return.Bound E (.nil a) s := by
  rintro x y ⟨z,rfl,hzy⟩
  exact h x y hzy

/-- `lem:foundational-typed-return-holonomy`: whole-word containment alone
derives all consecutive kernels and gives identity for EVERY coarser J. The
construction also covers the empty word, hence in particular n=1 and all
nonempty words with repeated original sorts. -/
theorem canonical_return_identity (s : Word G X a a)
    (h : ∀ x y, s.eval x y → E x y) :
    Return.holonomy E trans s (whole_bound E s h) = id ∧
      ∀ (J : InvEq G (X a)) (hEJ : E ≤ J),
        Return.holonomy J trans s
          (Return.coarser_bound E hEJ (.nil a) s (whole_bound E s h)) = id :=
  ⟨Return.holonomy_identity E trans s (whole_bound E s h),
    fun J hEJ => Return.all_coarser_holonomy E trans s (whole_bound E s h) J hEJ⟩

/-- Every actual cut, without new prefix-kernel assumptions. -/
theorem every_prefix_consumer (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y)
    {i : I} (p : Word G X a i) (s : Word G X i a)
    (h : ∀ x y, Word.eval (p.append s) x y → E x y) :
    ∃ T : Transport E p.eval,
      Function.Surjective T.label ∧
        ∀ y z, T.target y z ↔ ∃ x x', p.eval x y ∧ E x x' ∧ p.eval x' z := by
  have hb : Return.Bound E p s := by
    intro x y hxy
    apply h x y
    rw [Word.eval,TypedWord.eval_append]
    exact hxy
  exact ⟨Return.prefixTransport E trans p s hb,
    (Return.prefixTransport E trans p s hb).label_surjective,
    (Return.prefixTransport E trans p s hb).target_iff⟩
end ReturnConsumer
end CCO.QuotientTransport
