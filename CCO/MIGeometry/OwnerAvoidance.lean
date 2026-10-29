import CCO.AclOwners.HarmlessFullAut
import CCO.AclOwners.Avoidance
import CCO.AclOwners.ClosedAmalgamation
import CCO.MIGeometry.ActionClosure

/-! One simultaneous avoidance move fixing every named owner. Harmlessness
is stated for the full source automorphism group and transported only on
finite stabilizer orbits to the given homogeneous witness group. -/
universe v w t z q
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H

/-- Full harmlessness also permits any finite indexing of the named
classes; the `Fin n` convention does not restrict the collection. -/
theorem harmless_ownerAcl {K : ColourEq S ()} (harmless : FullHarmless S K)
    {I : Type z} [Finite I] (A : Finset M) (q : I → Quotient K.val) :
    OwnerAcl S (G := G) A (fun _ : I => K) q = Acl G A := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q' : Fin (Fintype.card I) → Quotient K.val := fun j => q (e.symm j)
  have h := harmless A (Fintype.card I) q'
  rw [fullOwnerAcl_eq S H,fullRealAcl_eq S H] at h
  have he : OwnerAcl S (G := G) A (fun _ : I => K) q =
      OwnerAcl S (G := G) A (fun _ : Fin (Fintype.card I) => K) q' := by
    ext x
    have horbit : ownerOrbit S (G := G) A (fun _ : I => K) q x =
        ownerOrbit S (G := G) A (fun _ : Fin (Fintype.card I) => K) q' x := by
      ext y
      constructor
      · rintro ⟨g,hg,hq,hxy⟩
        exact ⟨g,hg,fun j => hq (e.symm j),hxy⟩
      · rintro ⟨g,hg,hq,hxy⟩
        refine ⟨g,hg,?_,hxy⟩
        intro i
        simpa only [q',e.symm_apply_apply] using hq (e i)
    change Set.Finite _ ↔ Set.Finite _
    rw [horbit]
  exact he.trans h

/-- The actual subgroup fixing a finite real set and every displayed
quotient owner point. -/
def ownerFixer (K : ColourEq S ()) (A : Finset M)
    {I : Type z} (q : I → Quotient K.val) : Subgroup G := by
  letI := originalQuotientAction S H K
  exact {
    carrier := {g | (∀ a ∈ A, g • a = a) ∧ ∀ i, g • q i = q i}
    one_mem' := ⟨fun _ _ => one_smul _ _,fun _ => one_smul _ _⟩
    mul_mem' := by
      rintro g h ⟨hg,hgq⟩ ⟨hh,hhq⟩
      exact ⟨fun a ha => by rw [mul_smul,hh a ha,hg a ha],
        fun i => by rw [mul_smul,hhq i,hgq i]⟩
    inv_mem' := by
      rintro g ⟨hg,hgq⟩
      exact ⟨fun a ha => by rw [inv_smul_eq_iff,hg a ha],
        fun i => by rw [inv_smul_eq_iff,hgq i]⟩ }

/-- The subgroup's real orbit is exactly the actual finite owner orbit. -/
theorem ownerFixer_orbit (K : ColourEq S ()) (A : Finset M)
    {I : Type z} (q : I → Quotient K.val) (x : M) :
    MulAction.orbit (ownerFixer S H K A q) x =
      ownerOrbit S (G := G) A (fun _ : I => K) q x := by
  letI := originalQuotientAction S H K
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.val,g.property.1,fun i =>
      (fixesOwner_iff_quotient_fixed S H K (q i) g.val).mpr (g.property.2 i),rfl⟩
  · rintro ⟨g,hg,hq,rfl⟩
    exact ⟨⟨g,hg,fun i => (fixesOwner_iff_quotient_fixed S H K (q i) g).mp (hq i)⟩,rfl⟩

/-- C13: one group element fixes the base and ALL harmless actual owners,
while moving every requested off-base point outside the finite forbidden
set. Neither the extension nor the forbidden set has to be closed. -/
theorem harmless_owner_avoidance (K : ColourEq S ()) (harmless : FullHarmless S K)
    {I : Type z} [Finite I] (q : I → Quotient K.val)
    [DecidableEq M] (A L Z : Finset M) (closed : Closed G A) :
    letI := originalQuotientAction S H K
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧ (∀ i, g • q i = q i) ∧
      ∀ x ∈ L, x ∉ A → ∀ z ∈ Z, g • x ≠ z := by
  classical
  letI := originalQuotientAction S H K
  have horbit (x : M) (hx : x ∈ L \ A) :
      (MulAction.orbit (ownerFixer S H K A q) x).Infinite := by
    rw [ownerFixer_orbit S H]
    intro hfin
    have hxacl : x ∈ OwnerAcl S (G := G) A (fun _ : I => K) q := hfin
    rw [harmless_ownerAcl S H harmless A q,closed] at hxacl
    exact (Finset.mem_sdiff.mp hx).2 hxacl
  obtain ⟨g,hg⟩ := finite_action_avoidance (G := ownerFixer S H K A q) (L \ A) Z horbit
  refine ⟨g.val,g.property.1,g.property.2,?_⟩
  intro x hx hxA z hz
  exact hg x (Finset.mem_sdiff.mpr ⟨hx,hxA⟩) z hz

/-- The same avoidance theorem with any actual equivariant naming of the
owner quotient. A kernel identity replaces a choice of global section. -/
theorem harmless_owner_map_avoidance (K : ColourEq S ()) (harmless : FullHarmless S K)
    {O : Type q} [MulAction G O] (owner : M → O)
    (surj : Function.Surjective owner)
    (equiv : ∀ (g : G) x, owner (g • x) = g • owner x)
    (kernel : ∀ x y, K x y ↔ owner x = owner y)
    {I : Type z} [Finite I] (q : I → O)
    [DecidableEq M] (A L Z : Finset M) (closed : Closed G A) :
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧ (∀ i, g • q i = q i) ∧
      ∀ x ∈ L, x ∉ A → ∀ z ∈ Z, g • x ≠ z := by
  classical
  choose r hr using fun i => surj (q i)
  let qK : I → Quotient K.val := fun i => Quotient.mk'' (r i)
  letI := originalQuotientAction S H K
  obtain ⟨g,hA,hq,havoid⟩ := harmless_owner_avoidance S H K harmless qK A L Z closed
  refine ⟨g,hA,?_,havoid⟩
  intro i
  have he : K (g • r i) (r i) := Quotient.exact (hq i)
  have ho := (kernel _ _).mp he
  rw [equiv,hr] at ho
  exact ho

/-- C17: place both extensions over the original closed base, preserving
all actual owner labels and making their literal intersections the base.
The recipient helper need not be closed for this placement lemma. -/
theorem harmless_owner_map_two_placements (K : ColourEq S ()) (harmless : FullHarmless S K)
    {O : Type q} [MulAction G O] (owner : M → O)
    (surj : Function.Surjective owner)
    (equiv : ∀ (g : G) x, owner (g • x) = g • owner x)
    (kernel : ∀ x y, K x y ↔ owner x = owner y)
    {I : Type z} [Finite I] (q : I → O)
    [DecidableEq M] (A D L R : Finset M) (closed : Closed G A) :
    ∃ l r : G, (∀ a ∈ A, l • a = a) ∧ (∀ a ∈ A, r • a = a) ∧
      (∀ i, l • q i = q i) ∧ (∀ i, r • q i = q i) ∧
      (∀ x ∈ L, x ∉ A → l • x ∉ D) ∧
      (∀ y ∈ R, y ∉ A → r • y ∉ D) ∧
      (∀ x ∈ L, ∀ y ∈ R, l • x = r • y ↔ x = y ∧ x ∈ A) := by
  classical
  obtain ⟨l,hl,hlq,havoidL⟩ := harmless_owner_map_avoidance S H K harmless owner surj equiv kernel
    q A L (D \ A) closed
  obtain ⟨r,hr,hrq,havoidR⟩ := harmless_owner_map_avoidance S H K harmless owner surj equiv kernel
    q A R ((D \ A) ∪ (L.image (fun x => l • x) \ A)) closed
  have offL (x : M) (hx : x ∈ L) (hxA : x ∉ A) : l • x ∉ D := by
    intro hD
    have hA : l • x ∉ A := fun h => hxA ((smul_mem_iff_of_fixes l A hl x).mp h)
    exact havoidL x hx hxA (l • x) (Finset.mem_sdiff.mpr ⟨hD,hA⟩) rfl
  have offR (y : M) (hy : y ∈ R) (hyA : y ∉ A) : r • y ∉ D := by
    intro hD
    have hA : r • y ∉ A := fun h => hyA ((smul_mem_iff_of_fixes r A hr y).mp h)
    exact havoidR y hy hyA (r • y)
      (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hD,hA⟩)) rfl
  refine ⟨l,r,hl,hr,hlq,hrq,offL,offR,?_⟩
  intro x hx y hy
  constructor
  · intro he
    have hyA : y ∈ A := by
      by_contra hn
      have hyA' : r • y ∉ A := fun h => hn ((smul_mem_iff_of_fixes r A hr y).mp h)
      apply havoidR y hy hn (r • y) (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨x,hx,he⟩,hyA'⟩))
      rfl
    have hxA : x ∈ A := (smul_mem_iff_of_fixes l A hl x).mp (by rw [he,hr y hyA]; exact hyA)
    rw [hl x hxA,hr y hyA] at he
    exact ⟨he,hxA⟩
  · rintro ⟨he,hxA⟩
    rw [hl x hxA,hr y (he ▸ hxA),he]

end CCO.MIGeometry
