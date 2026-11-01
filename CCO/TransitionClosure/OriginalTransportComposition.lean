import CCO.TransitionClosure.OriginalTransportUpwardRewrite
import CCO.QuotientTransport.Consumers

/-!
# B049 source07 C33-C34: ORIGINAL typed RAW quotient transition composition

This is a source-actual application of the accepted B040 generic
transport/composition API. The ORIGINAL finite homogeneous
source supplies transitivity on all three named original sorts.
The first intermediate kernel is LITERALLY Rᵒᵖ;J;R.
The second relation Q satisfies Q;Qᵒᵖ ⊆ that same kernel,
not an unrelated chart.

The composite R;Q has its TRUE RAW source-kernel condition
and target kernel Qᵒᵖ;(Rᵒᵖ;J;R);Q; both its quotient
map and its endpoint kernel are equal to composing
the two canonical transport maps on the SAME quotient carriers.

No original SAP, CCO, full NR2, quotient SAP, new axioms,
mixed-sort commutation or artificial positive identity.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- SOURCE07 C33/C34 TQC: for actual original invariant RAW
R:i→j and Q:j→k, the original source J-bounded
R;Rᵒᵖ and the LITERAL intermediate bound
Q;Qᵒᵖ⊆Rᵒᵖ;J;R produce canonical transports T and U.
The source product R;Q is a genuine composite transport
with exactly U.target as target kernel, and its quotient map
is POINTWISE the composition of the original quotient maps.

All three original named sorts may differ. No quotient
action/source is assumed beyond the SAME old G on X.
-/
theorem original_source_raw_quotient_transitions_compose
    (H : HomogeneousSource S G)
    {i j k : ι} (J : ColourEq S i)
    (R : Rel (X i) (X j)) (Q : Rel (X j) (X k))
    (hRInv : Invariant (G := G) R)
    (hRNonempty : ∃ x : X i, ∃ y : X j, R x y)
    (hRKernel : ∀ x x' : X i,
      (∃ y : X j, R x y ∧ R x' y) → J x x')
    (hQInv : Invariant (G := G) Q)
    (hQNonempty : ∃ y : X j, ∃ z : X k, Q y z)
    (hQKernel : ∀ y y' : X j,
      (∃ z : X k, Q y z ∧ Q y' z) →
        ∃ x x' : X i, R x y ∧ J x x' ∧ R x' y') :
    ∃ T : Transport (originalColourEqAsInvEq S H J) R,
      ∃ U : Transport T.target Q,
        ((T.composite U).target = U.target) ∧
        (∀ q : Quotient J.val,
          InvEq.quotientCongr (T.composite_target U)
            ((T.composite U).quotientEquiv q) =
              U.quotientEquiv (T.quotientEquiv q)) ∧
        (∀ z z' : X k,
          (T.composite U).target z z' ↔
            ∃ x x' : X i,
              (∃ y : X j, R x y ∧ Q y z) ∧
              J x x' ∧
              (∃ y' : X j, R x' y' ∧ Q y' z')) := by
  let E : InvEq G (X i) := originalColourEqAsInvEq S H J
  let T : Transport E R :=
    typed_quotient_transport E R hRInv hRNonempty
      (S.original_sort_transitive_of_homogeneous H i)
      (S.original_sort_transitive_of_homogeneous H j)
      (fun x x' hx => hRKernel x x' hx)
  let U : Transport T.target Q :=
    typed_quotient_transport T.target Q hQInv hQNonempty
      (S.original_sort_transitive_of_homogeneous H j)
      (S.original_sort_transitive_of_homogeneous H k)
      (fun y y' hy => (T.target_iff y y').mpr (hQKernel y y' hy))
  refine ⟨T,U,T.composite_target U,?_,?_⟩
  · intro q
    exact T.composite_quotient U q
  · intro z z'
    exact (T.composite U).target_iff z z'

end CCO.TransitionClosure
