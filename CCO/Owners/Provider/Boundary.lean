import CCO.Owners.Provider.Canonical

/-! Empty owner systems and literal identity quotients. These branches
need no EPPA, countability, CCO, SAP, or auxiliary duplicate identity sort. -/
universe v w t
namespace CCO.Owners.Provider
open Product
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]

/-- Over an empty owner set the original real input and witness are empty.
All automorphism requests and quotient actions are handled directly. -/
theorem empty_owner_witness
    (S : AtomicSource.{0,v,w} Unit (fun _ => A)) (H : HomogeneousSource S G)
    (π : A → O) (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (T : Set A) (overT : ∀ x : T, π x.val ∈ (∅ : Set O)) :
    Nonempty (OwnerWitness S H π equivπ ∅ T overT) := by
  have inc : T ⊆ (∅ : Set A) := fun x hx => (overT ⟨x,hx⟩).elim
  have over : ∀ x : (∅ : Set A), π x.val ∈ (∅ : Set O) := fun x => x.property.elim
  have onto : Function.Surjective (ownerProjection π ∅ ∅ over) := fun b => b.property.elim
  refine ⟨⟨∅,Set.finite_empty,inc,?_,over,onto,?_,?_,?_,?_⟩⟩
  · intro x hx
    exact hx.elim
  · intro r
    refine ⟨1,?_,Subsingleton.elim _ _⟩
    intro x
    exact (overT x.val).elim
  · intro x
    exact x.property.elim
  · intro γ
    exact ⟨1,Subsingleton.elim _ _⟩
  · intro x
    exact x.property.elim

/-- If the projection is literal identity, compatibility already says
that the partial real map agrees with gamma on its whole domain. The
same finite B is the fixed-base witness for ALL such requests. -/
theorem identity_fixed_base (T B : Set A) (overT : ∀ x : T, x.val ∈ B)
    (r : OwnerRequest (G := G) (id : A → A) T B overT) :
    ∃ β : OrbitalAut G A (Subtype.val : B → A),
      (∀ x : r.part.domain,
        (β.val ⟨x.val.val,overT x.val⟩).val = (r.part.map x).val) ∧ β = r.owner := by
  refine ⟨r.owner,?_,rfl⟩
  intro x
  exact (r.compatible x).symm

end CCO.Owners.Provider
