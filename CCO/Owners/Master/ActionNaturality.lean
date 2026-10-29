import CCO.Owners.Product.ActionConsumers

/-! The homomorphism obtained from a product presentation is the genuine
natural finite quotient action. Point equivariance and ONTO carriers prove
this equality; an abstract group isomorphism alone is not substituted. -/

namespace CCO.Owners.Master
open Product

variable {G A B U V : Type*} [Group G] [MulAction G A] [MulAction G B]
variable {ι : U → A} {κ : V → B}
variable (Q : OrbitalQuotient (G := G) ι κ)

theorem orbital_quotient_action_unique
    (ρ : OrbitalAut G A ι →* OrbitalAut G B κ)
    (equiv : ∀ g x, ρ g • Q.projection x = Q.projection (g • x)) :
    ρ = Q.action := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := Q.surjective y
  exact (equiv g x).trans (Q.action_projection g x).symm

variable {K H X Y : Type*} [Group K] [Group H] [MulAction K X] [MulAction H Y]
variable (E : ActionEquivalence (OrbitalAut G A ι) K U X)
variable (F : ActionEquivalence (OrbitalAut G B κ) H V Y)

theorem actual_onto_kernel_of_commuting (ρ : K →* H) (π : X → Y)
    (equivπ : ∀ g x, π (g • x) = ρ g • π x)
    (commutes : ∀ x, F.point (Q.projection x) = π (E.point x))
    (h : Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π) :
    Function.Surjective Q.action ∧ GroupActions.FibreTransitive Q.action Q.projection := by
  have hQ : Q.projection = E.transportedMap F π := by
    funext x
    apply F.point.injective
    exact (commutes x).trans (E.transportedMap_commutes F π x).symm
  have heq : E.transportedHom F ρ = Q.action := by
    apply orbital_quotient_action_unique Q
    intro g x
    rw [hQ]
    exact (E.transported_equivariant F ρ π equivπ g x).symm
  have result := E.onto_kernel_of_commuting F ρ π Q.projection commutes h
  rw [heq] at result
  exact result

theorem actual_prescribed_of_commuting (ρ : K →* H) (π : X → Y)
    (equivπ : ∀ g x, π (g • x) = ρ g • π x)
    (commutes : ∀ x, F.point (Q.projection x) = π (E.point x))
    (h : GroupActions.PrescribedLift ρ π) :
    GroupActions.PrescribedLift Q.action Q.projection := by
  have hQ : Q.projection = E.transportedMap F π := by
    funext x
    apply F.point.injective
    exact (commutes x).trans (E.transportedMap_commutes F π x).symm
  have heq : E.transportedHom F ρ = Q.action := by
    apply orbital_quotient_action_unique Q
    intro g x
    rw [hQ]
    exact (E.transported_equivariant F ρ π equivπ g x).symm
  have result := E.prescribed_of_commuting F ρ π Q.projection commutes h
  rw [heq] at result
  exact result

end CCO.Owners.Master
