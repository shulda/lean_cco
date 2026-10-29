import CCO.FiniteKernel.BinarySource

/-! Genuine unary/binary-language quotient descent. The recognized kernel
and ALL target relation pullbacks are pair-profile invariants; no ambient
orbital group, homogeneity, countability, or automorphism-lifting provider
is needed. Full groups are the accepted `BinaryStructure.Aut` groups. -/

namespace CCO.Owners.Joint.Relational
open CCO.FiniteKernel

variable {U V : Type*}

/-- Equality-inclusive complete pair profiles, with preservation AND
reflection of every named unary and binary relation. -/
structure SamePair (S : BinaryStructure U) (a b x y : U) : Prop where
  equal : x = y ↔ a = b
  unary_left : ∀ r, S.unary r x ↔ S.unary r a
  unary_right : ∀ r, S.unary r y ↔ S.unary r b
  binary : ∀ r, S.binary r x y ↔ S.binary r a b

namespace SamePair
variable {S : BinaryStructure U} {a b x y z t : U}

theorem refl (a b : U) : SamePair S a b a b :=
  ⟨Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem symm (h : SamePair S a b x y) : SamePair S x y a b :=
  ⟨h.equal.symm, fun r => (h.unary_left r).symm,
    fun r => (h.unary_right r).symm, fun r => (h.binary r).symm⟩

theorem trans (h : SamePair S a b x y) (k : SamePair S x y z t) : SamePair S a b z t :=
  ⟨k.equal.trans h.equal, fun r => (k.unary_left r).trans (h.unary_left r),
    fun r => (k.unary_right r).trans (h.unary_right r),
    fun r => (k.binary r).trans (h.binary r)⟩
end SamePair

/-- Every FULL structure automorphism preserves complete pair profiles. -/
theorem aut_pair {S : BinaryStructure U} (g : S.Aut) (x y : U) :
    SamePair S x y (g.val x) (g.val y) :=
  ⟨g.val.injective.eq_iff, fun r => g.unary r x, fun r => g.unary r y, fun r => g.binary r x y⟩

/-- Complete pair preservation gives membership in the accepted full
structural group; unary predicates are recovered on diagonal pairs. -/
theorem samePair_mem_aut {S : BinaryStructure U} (p : Equiv.Perm U)
    (h : ∀ x y, SamePair S x y (p x) (p y)) : p ∈ S.autGroup :=
  ⟨fun r x => (h x x).unary_left r, fun r x y => (h x y).binary r⟩

/-- A genuine arbitrary-domain induced partial isomorphism. -/
structure Partial (S : BinaryStructure U) where
  domain : Set U
  map : domain → U
  injective : Function.Injective map
  pair : ∀ x y : domain, SamePair S x.val y.val (map x) (map y)

namespace Partial
variable {S : BinaryStructure U} (p : Partial S)

def Extends (g : S.Aut) : Prop := ∀ x, g.val x.val = p.map x

theorem unary_iff (r : S.Unary) (x : p.domain) :
    S.unary r (p.map x) ↔ S.unary r x.val := (p.pair x x).unary_left r

theorem binary_iff (r : S.Binary) (x y : p.domain) :
    S.binary r (p.map x) (p.map y) ↔ S.binary r x.val y.val := (p.pair x y).binary r
end Partial

/-- Operational old-colour-union data for a genuine quotient. Kernel
recognition and target pair-profile recognition are separate requirements;
neither one asserts any lifting of an automorphism. -/
structure RecognizableQuotient (S : BinaryStructure U) (T : BinaryStructure V) where
  projection : U → V
  surjective : Function.Surjective projection
  kernel : ∀ a b x y, SamePair S a b x y →
    (projection x = projection y ↔ projection a = projection b)
  pair : ∀ a b x y, SamePair S a b x y →
    SamePair T (projection a) (projection b) (projection x) (projection y)

namespace RecognizableQuotient
variable {S : BinaryStructure U} {T : BinaryStructure V}
variable (Q : RecognizableQuotient S T)

theorem kernel_iff (g : S.Aut) (x y : U) :
    Q.projection (g.val x) = Q.projection (g.val y) ↔ Q.projection x = Q.projection y :=
  Q.kernel x y _ _ (aut_pair g x y)

noncomputable def map (g : S.Aut) (v : V) : V :=
  Q.projection (g.val (Classical.choose (Q.surjective v)))

@[simp] theorem map_projection (g : S.Aut) (x : U) :
    Q.map g (Q.projection x) = Q.projection (g.val x) :=
  (Q.kernel_iff g _ x).mpr (Classical.choose_spec (Q.surjective (Q.projection x)))

noncomputable def perm (g : S.Aut) : Equiv.Perm V where
  toFun := Q.map g
  invFun := Q.map g⁻¹
  left_inv := by
    intro v
    obtain ⟨x, rfl⟩ := Q.surjective v
    rw [Q.map_projection, Q.map_projection]
    simp
  right_inv := by
    intro v
    obtain ⟨x, rfl⟩ := Q.surjective v
    rw [Q.map_projection, Q.map_projection]
    simp

noncomputable def aut (g : S.Aut) : T.Aut := by
  refine ⟨Q.perm g, ?_⟩
  constructor
  · intro r v
    obtain ⟨x, rfl⟩ := Q.surjective v
    change T.unary r (Q.map g (Q.projection x)) ↔ T.unary r (Q.projection x)
    rw [Q.map_projection]
    exact (Q.pair x x _ _ (aut_pair g x x)).unary_left r
  · intro r v w
    obtain ⟨x, rfl⟩ := Q.surjective v
    obtain ⟨y, rfl⟩ := Q.surjective w
    change T.binary r (Q.map g (Q.projection x)) (Q.map g (Q.projection y)) ↔ _
    rw [Q.map_projection, Q.map_projection]
    exact (Q.pair x y _ _ (aut_pair g x y)).binary r

@[simp] theorem aut_projection (g : S.Aut) (x : U) :
    (Q.aut g).val (Q.projection x) = Q.projection (g.val x) := Q.map_projection g x

/-- Honest quotient action of the ENTIRE source structural group. -/
noncomputable def action : S.Aut →* T.Aut where
  toFun := Q.aut
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro v
    obtain ⟨x, rfl⟩ := Q.surjective v
    exact Q.aut_projection 1 x
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro v
    obtain ⟨x, rfl⟩ := Q.surjective v
    change (Q.aut (g * h)).val (Q.projection x) =
      (Q.aut g).val ((Q.aut h).val (Q.projection x))
    rw [Q.aut_projection, Q.aut_projection, Q.aut_projection]
    rfl

@[simp] theorem action_projection (g : S.Aut) (x : U) :
    (Q.action g).val (Q.projection x) = Q.projection (g.val x) := Q.aut_projection g x

variable (p : Partial S)

/-- The actual image of this partial map's own domain, including empty. -/
def projectedDomain : Set V := Q.projection '' p.domain

noncomputable def domainLift (v : Q.projectedDomain p) : p.domain :=
  ⟨Classical.choose v.property, (Classical.choose_spec v.property).1⟩

@[simp] theorem projection_domainLift (v : Q.projectedDomain p) :
    Q.projection (Q.domainLift p v).val = v.val := (Classical.choose_spec v.property).2

theorem partial_kernel_iff (x y : p.domain) :
    Q.projection (p.map x) = Q.projection (p.map y) ↔
      Q.projection x.val = Q.projection y.val :=
  Q.kernel x.val y.val _ _ (p.pair x y)

/-- Genuine induced partial isomorphism on its precise projected domain. -/
noncomputable def projectedPartial : Partial T where
  domain := Q.projectedDomain p
  map v := Q.projection (p.map (Q.domainLift p v))
  injective := by
    intro v w hvw
    apply Subtype.ext
    have h := (Q.partial_kernel_iff p _ _).mp hvw
    simpa only [Q.projection_domainLift] using h
  pair v w := by
    have h := Q.pair _ _ _ _ (p.pair (Q.domainLift p v) (Q.domainLift p w))
    simpa only [Q.projection_domainLift] using h

@[simp] theorem partial_projection (x : p.domain) :
    (Q.projectedPartial p).map ⟨Q.projection x.val, ⟨x.val, x.property, rfl⟩⟩ =
      Q.projection (p.map x) := by
  apply (Q.partial_kernel_iff p _ _).mpr
  exact Q.projection_domainLift p _

/-- Projection has EXACTLY the image of the original actual range. -/
theorem partial_range_eq :
    Set.range (Q.projectedPartial p).map = Q.projection '' Set.range p.map := by
  apply Set.ext
  intro v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨p.map (Q.domainLift p x), ⟨Q.domainLift p x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨Q.projection x.val, ⟨x.val, x.property, rfl⟩⟩, Q.partial_projection p x⟩

theorem partial_domain_subset {a : Set U} (h : p.domain ⊆ a) :
    (Q.projectedPartial p).domain ⊆ Q.projection '' a := by
  rintro v ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem partial_mapsTo {a : Set U} (h : ∀ x, p.map x ∈ a) :
    ∀ v, (Q.projectedPartial p).map v ∈ Q.projection '' a := by
  intro v
  exact ⟨p.map (Q.domainLift p v), h _, rfl⟩

theorem partial_extends (g : S.Aut) (h : p.Extends g) :
    (Q.projectedPartial p).Extends (Q.action g) := by
  intro v
  obtain ⟨x, hx, hxv⟩ := v.property
  have hv : v = ⟨Q.projection x, ⟨x, hx, rfl⟩⟩ := Subtype.ext hxv.symm
  subst v
  let x' : p.domain := ⟨x, hx⟩
  rw [Q.action_projection, Q.partial_projection p x']
  exact congrArg Q.projection (h x')

end RecognizableQuotient

/-- Ordinary arbitrary partial-map extension on one induced input. -/
def EPPAFor (S : BinaryStructure U) (a : Set U) : Prop :=
  ∀ p : Partial S, p.domain ⊆ a → (∀ x, p.map x ∈ a) → ∃ g : S.Aut, p.Extends g

/-- EVERY compatible partial map has EVERY prescribed entire owner action. -/
def PrescribedEPPAFor {S : BinaryStructure U} {T : BinaryStructure V}
    (Q : RecognizableQuotient S T) (a : Set U) : Prop :=
  ∀ p : Partial S, p.domain ⊆ a → (∀ x, p.map x ∈ a) → ∀ δ : T.Aut,
    (∀ x, Q.projection (p.map x) = δ.val (Q.projection x.val)) →
      ∃ g : S.Aut, p.Extends g ∧ Q.action g = δ

end CCO.Owners.Joint.Relational
