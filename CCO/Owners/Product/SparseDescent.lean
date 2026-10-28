import CCO.Owners.Product.Descent

/-! Genuine coordinate partial isomorphisms from an arbitrary sparse
original domain. Both named kernels AND quotient pair-colour pullbacks are
proved from actual original-action orbitals. -/
namespace CCO.Owners.Product
variable {G A B U V : Type*} [Group G] [MulAction G A] [MulAction G B]

structure OrbitalPartial (ι : U → A) where
  domain : Set U
  map : domain → U
  injective : Function.Injective map
  pair : ∀ x y : domain, GroupActions.orbital (G := G)
    (ι x.val) (ι y.val) (ι (map x)) (ι (map y))

namespace OrbitalPartial
variable {ι : U → A} (p : OrbitalPartial (G := G) ι)

def Extends (g : OrbitalAut G A ι) : Prop := ∀ x, g.val x.val = p.map x

theorem relation_iff (r : A × A) (x y : p.domain) :
    (orbitalStructure G A ι).binary r (p.map x) (p.map y) ↔
      (orbitalStructure G A ι).binary r x.val y.val := by
  change GroupActions.orbital (G := G) r.1 r.2 (ι (p.map x)) (ι (p.map y)) ↔
    GroupActions.orbital (G := G) r.1 r.2 (ι x.val) (ι y.val)
  have he := GroupActions.orbital_eq_of_mem _ _ _ _ (p.pair x y)
  constructor
  · intro hh
    have h' := GroupActions.orbital_eq_of_mem _ _ _ _ hh
    rw [h'.trans he.symm]
    exact GroupActions.orbital_nonempty _ _
  · rintro ⟨g,hgx,hgy⟩
    obtain ⟨h,hhx,hhy⟩ := p.pair x y
    exact ⟨h*g,by simpa only [mul_smul,hgx] using hhx,
      by simpa only [mul_smul,hgy] using hhy⟩

end OrbitalPartial

namespace OrbitalQuotient
variable {ι : U → A} {κ : V → B} (Q : OrbitalQuotient (G := G) ι κ)
variable (p : OrbitalPartial (G := G) ι)

def projectedDomain : Set V := Q.projection '' p.domain

noncomputable def domainLift (v : Q.projectedDomain p) : p.domain :=
  ⟨Classical.choose v.property,(Classical.choose_spec v.property).1⟩

@[simp] theorem projection_domainLift (v : Q.projectedDomain p) :
    Q.projection (Q.domainLift p v).val = v.val := (Classical.choose_spec v.property).2

theorem partial_kernel_iff (x y : p.domain) :
    Q.projection (p.map x) = Q.projection (p.map y) ↔
      Q.projection x.val = Q.projection y.val := by
  rw [← Q.target_injective.eq_iff,← Q.target_injective.eq_iff]
  simp only [Q.commutes]
  exact equivariant_kernel_iff Q.ambient Q.equivariant (p.pair x y)

noncomputable def projectedPartial : OrbitalPartial (G := G) κ where
  domain := Q.projectedDomain p
  map v := Q.projection (p.map (Q.domainLift p v))
  injective := by
    intro v w hvw
    apply Subtype.ext
    have h := (Q.partial_kernel_iff p _ _).mp hvw
    simpa only [Q.projection_domainLift] using h
  pair v w := by
    have h := equivariant_pair Q.ambient Q.equivariant
      (p.pair (Q.domainLift p v) (Q.domainLift p w))
    simpa only [← Q.commutes,Q.projection_domainLift] using h

@[simp] theorem partial_projection (x : p.domain) :
    (Q.projectedPartial p).map ⟨Q.projection x.val,⟨x.val,x.property,rfl⟩⟩ =
      Q.projection (p.map x) := by
  apply (Q.partial_kernel_iff p _ _).mpr
  exact Q.projection_domainLift p _

theorem partial_domain_subset {a : Set U} (h : p.domain ⊆ a) :
    (Q.projectedPartial p).domain ⊆ Q.projection '' a := by
  rintro v ⟨x,hx,rfl⟩
  exact ⟨x,h hx,rfl⟩

theorem partial_mapsTo {a : Set U} (h : ∀ x, p.map x ∈ a) :
    ∀ v, (Q.projectedPartial p).map v ∈ Q.projection '' a := by
  intro v
  exact ⟨p.map (Q.domainLift p v),h _,rfl⟩

theorem partial_extends (g : OrbitalAut G A ι) (h : p.Extends g) :
    (Q.projectedPartial p).Extends (Q.action g) := by
  intro v
  obtain ⟨x,hx,hxv⟩ := v.property
  have hv : v = ⟨Q.projection x,⟨x,hx,rfl⟩⟩ := Subtype.ext hxv.symm
  subst v
  let x' : p.domain := ⟨x,hx⟩
  change (Q.action g).val (Q.projection x) = (Q.projectedPartial p).map ⟨Q.projection x,_⟩
  rw [Q.action_projection,Q.partial_projection p x']
  exact congrArg Q.projection (h x')

end OrbitalQuotient

/-- Ordinary finite-witness EPPA for the displayed original induced set.
The ambient witness may be arbitrary; callers explicitly supply finiteness. -/
def EPPAFor {ι : U → A} (a : Set U) : Prop :=
  ∀ p : OrbitalPartial (G := G) ι, p.domain ⊆ a →
    (∀ x, p.map x ∈ a) → ∃ g : OrbitalAut G A ι, p.Extends g

/-- The full ENTIRE owner action is prescribed, not just old domain owners. -/
def PrescribedEPPAFor {ι : U → A} {κ : V → B}
    (Q : OrbitalQuotient (G := G) ι κ) (a : Set U) : Prop :=
  ∀ (p : OrbitalPartial (G := G) ι), p.domain ⊆ a → (∀ x, p.map x ∈ a) →
    ∀ δ : OrbitalAut G B κ,
    (∀ x, Q.projection (p.map x) = δ.val (Q.projection x.val)) →
    ∃ g : OrbitalAut G A ι, p.Extends g ∧ Q.action g = δ

end CCO.Owners.Product
