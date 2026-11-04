import CCO.UnaryTermsReturn.StabilizerTransport

/-!
# B052 source10 C25 — stabilizer equivalence for named quotient terms

The source's phrase "any automorphism group" means a group that
really preserves the ACTUAL named unary functions and their
quotient interpretations. No transitivity, faithfulness, old
SAP/CCO, hidden SAP or homogeneity is needed for the elementary
stabilizer equivalence once the source10 named normal form
theta is known to be an equivariant INJECTION.

This general theorem is intentionally separate from the
old-G B040 transport instance; it does not pretend an unrelated
group action preserves the finite hidden language.
-/

universe u v w
namespace CCO.UnaryTermsReturn

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w}
variable [MulAction G A] [MulAction G B]

/-- With the ACTUAL equivariance and injectivity hypotheses,
a named quotient-coordinate value has the same stabilizer
as its preimage for ANY acting group, without faithfulness,
transitivity or a choice of quotient representative. -/
theorem equivariant_injective_named_value_stabilizer
    (theta : A → B)
    (hInjective : Function.Injective theta)
    (hEquivariant : ∀ (g : G) (a : A),
      theta (g • a) = g • theta a)
    (g : G) (a : A) :
    (g • theta a = theta a) ↔ (g • a = a) := by
  constructor
  · intro hFix
    apply hInjective
    calc
      theta (g • a) = g • theta a := hEquivariant g a
      _ = theta a := hFix
  · intro hFix
    calc
      g • theta a = theta (g • a) :=
        (hEquivariant g a).symm
      _ = theta a := congrArg theta hFix

/-- If named real projection F_K is literally the actual
quotient map x ↦ [x]_K, its stabilizer equivalence is exactly
the preceding theorem specialized to the genuinely named
equivariant quotient normal map theta:K→F. This is conditional
on the actual named equivariance, not on an arbitrary subgroup
merely preserving the old fine colours. -/
theorem equivariant_quotient_named_normal_stabilizer
    (theta : A → B)
    (hInjective : Function.Injective theta)
    (hEquivariant : ∀ (g : G) (a : A),
      theta (g • a) = g • theta a) :
    ∀ (g : G) (a : A),
      g • theta a = theta a ↔ g • a = a :=
  equivariant_injective_named_value_stabilizer theta
    hInjective hEquivariant

end CCO.UnaryTermsReturn
