import CCO.QuotientTransport.Core
import CCO.TransitionClosure.OriginalTransportTargetFull

/-!
# B052 C23/C25: exact kernel and stabilizers of actual quotient maps

An actual B040 canonical transport is a bijection of quotient
carriers, equivariant under the SAME original acting group G.
Its source pointwise quotient kernel and the stabilizer of an
interpreted quotient position are therefore preserved exactly,
with no action of a separately postulated hidden automorphism
group, no faithfulness, no hidden SAP or quotient homogeneity.

For the source10 real-term normal form, the source equivalence K
is produced independently as an ACTUAL named proper FULL MI.
These lemmas provide the exact transport/bijection step, not the
additional named-term factorization or arbitrary-group extension.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w}
variable [MulAction G A] [MulAction G B]

open CCO.QuotientTransport

/-- For any actual G-invariant RAW quotient transport, equality
of output quotient classes of two source real points is exactly
the SOURCE input invariant equivalence, because the canonical
transport quotient map is an actual bijection. -/
theorem generic_transport_quotient_exact_kernel
    {E : InvEq G A} {R : CCO.QuotientTransport.Rel A B}
    (T : Transport E R) (x y : A) :
    T.quotientEquiv (Quotient.mk E.val x) =
      T.quotientEquiv (Quotient.mk E.val y) ↔ E x y := by
  constructor
  · intro h
    exact Quotient.exact (T.quotientEquiv.injective h)
  · intro h
    exact congrArg T.quotientEquiv (Quotient.sound h)

/-- Pointwise stabilizers in the ORIGINAL G of a quotient class
and its canonical transported quotient value agree. This
uses true G-equivariance of B040, not an assumed action on
arbitrary hidden partial isomorphisms. -/
theorem generic_transport_quotient_stabilizer
    {E : InvEq G A} {R : CCO.QuotientTransport.Rel A B}
    (T : Transport E R) (g : G) (q : Quotient E.val) :
    T.target.act g (T.quotientEquiv q) = T.quotientEquiv q ↔
      E.act g q = q := by
  constructor
  · intro h
    apply T.quotientEquiv.injective
    calc
      T.quotientEquiv (E.act g q) =
          T.target.act g (T.quotientEquiv q) :=
        T.quotientEquiv_equivariant g q
      _ = T.quotientEquiv q := h
  · intro h
    calc
      T.target.act g (T.quotientEquiv q) =
          T.quotientEquiv (E.act g q) :=
        (T.quotientEquiv_equivariant g q).symm
      _ = T.quotientEquiv q := congrArg T.quotientEquiv h

variable {ι : Type t} {X : ι → Type v}
variable (S : AtomicSource.{t,v,w} ι X)
variable [∀ i : ι, MulAction G (X i)]

/-- Source10 C23, full original J-kernel of an ACTUAL
original-G quotient transition. This applies across mixed
original source/target sorts without identifying their points. -/
theorem original_raw_transport_real_kernel
    (H : HomogeneousSource S G)
    {i j : ι} (J : ParityHasse.Original.ColourEq S i)
    {R : CCO.QuotientTransport.Rel (X i) (X j)}
    (T : Transport
      (TransitionClosure.originalColourEqAsInvEq S H J) R)
    (x y : X i) :
    T.quotientEquiv (Quotient.mk J.val x) =
      T.quotientEquiv (Quotient.mk J.val y) ↔ J x y :=
  generic_transport_quotient_exact_kernel T x y

end CCO.UnaryTermsReturn
