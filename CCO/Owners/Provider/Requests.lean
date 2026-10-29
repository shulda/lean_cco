import CCO.Owners.Provider.Induced

/-! All finite compatible owner requests, including the empty real map
with an arbitrary ENTIRE owner action, and singleton prescriptions. -/
namespace CCO.Owners.Provider
open Product
variable {G A O : Type*} [Group G] [MulAction G A] [MulAction G O]

structure OwnerRequest (π : A → O) (D : Set A) (B : Set O)
    (hD : ∀ x : D, π x.val ∈ B) where
  part : OrbitalPartial (G := G) (Subtype.val : D → A)
  owner : OrbitalAut G O (Subtype.val : B → O)
  compatible : ∀ x : part.domain,
    π (part.map x).val = (owner.val (ownerProjection π D B hD x.val)).val

instance finite_ownerRequest (π : A → O) (D : Set A) (B : Set O)
    [Finite D] [Finite B] (hD : ∀ x : D, π x.val ∈ B) :
    Finite (OwnerRequest (G := G) π D B hD) := by
  let f : OwnerRequest (G := G) π D B hD →
      OrbitalPartial (G := G) (Subtype.val : D → A) ×
        OrbitalAut G O (Subtype.val : B → O) := fun r => (r.part,r.owner)
  apply Finite.of_injective f
  intro p q hpq
  cases p
  cases q
  cases hpq
  rfl

def emptyRequest (π : A → O) (D : Set A) (B : Set O)
    (hD : ∀ x : D, π x.val ∈ B)
    (γ : OrbitalAut G O (Subtype.val : B → O)) :
    OwnerRequest (G := G) π D B hD where
  part := {
    domain := ∅
    map := fun x => False.elim x.property
    injective := fun x => False.elim x.property
    pair := fun x => False.elim x.property }
  owner := γ
  compatible := fun x => False.elim x.property

/-- Every compatible singleton request really belongs to the same
finite all-request type; transitivity supplies its diagonal orbital. -/
def singletonRequest (trans : ∀ x y : A, ∃ g : G, g • x = y)
    (π : A → O) (D : Set A) (B : Set O)
    (hD : ∀ x : D, π x.val ∈ B) (a a' : D)
    (γ : OrbitalAut G O (Subtype.val : B → O))
    (hγ : γ.val (ownerProjection π D B hD a) = ownerProjection π D B hD a') :
    OwnerRequest (G := G) π D B hD where
  part := {
    domain := {a}
    map := fun _ => a'
    injective := by
      intro x y _
      exact Subtype.ext ((Set.mem_singleton_iff.mp x.property).trans
        (Set.mem_singleton_iff.mp y.property).symm)
    pair := by
      intro x y
      have hx : x.val = a := Set.mem_singleton_iff.mp x.property
      have hy : y.val = a := Set.mem_singleton_iff.mp y.property
      obtain ⟨g,hg⟩ := trans a.val a'.val
      exact ⟨g,by simpa only [hx] using hg,by simpa only [hy] using hg⟩ }
  owner := γ
  compatible := by
    intro x
    have hx : x.val = a := Set.mem_singleton_iff.mp x.property
    simpa only [hx,ownerProjection] using (congrArg Subtype.val hγ).symm

end CCO.Owners.Provider
