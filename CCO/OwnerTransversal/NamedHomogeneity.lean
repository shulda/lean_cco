import CCO.OwnerTransversal.NamedSource
import CCO.OwnerTransversal.TypedLifting

/-! Joint real/owner lifting is used only after the named-closure orbit
argument.  Every displayed owner is retained, even if no real-domain
point lies over it. -/

universe v w t z r
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)

/-- C24's full finite joint lifting, with all mixed pairs discharged by
the generic exact-owner lift.  No global section is claimed. -/
theorem residual_joint_lifting {I : Type z} [Finite I] {J : Type r} [Finite J]
    (source target : I → M) (q q' : J → Owner S H R)
    (hReal : ∀ i j, col S (source i) (source j) = col S (target i) (target j))
    (hOwners : letI := originalQuotientAction S H R.E
      ∀ j k, GroupActions.orbital (G := G) (q j) (q k) (q' j) (q' k))
    (hCover : ∀ i, ∃ j, q j = owner S H R (source i) ∧
      q' j = owner S H R (target i)) :
    letI := originalQuotientAction S H R.E
    ∃ g : G, (∀ i, g • source i = target i) ∧ (∀ j, g • q j = q' j) :=
  finite_real_owner_lifting S H R.cco R.E R.exact source target q q' hReal hOwners hCover

/-- The full actual named-owner induced structure is homogeneous.  Empty
real domains and empty owner collections are included. -/
theorem named_homogeneous (B : Finset (Owner S H R)) :
    (namedStructure S H R B).Homogeneous := by
  classical
  intro A f _ hu hb
  letI := originalQuotientAction S H R.E
  let source : ↥A → M := fun a => a.val.val
  let target : ↥A → M := fun a => (f a).val
  let q : ↥B → Owner S H R := Subtype.val
  have hReal : ∀ i j, col S (source i) (source j) = col S (target i) (target j) := by
    intro i j
    exact ((hb (col S (source i) (source j)) i j).mpr rfl).symm
  have hCover : ∀ i, ∃ j, q j = owner S H R (source i) ∧
      q j = owner S H R (target i) := by
    intro i
    refine ⟨⟨owner S H R i.val.val,i.val.property⟩,rfl,?_⟩
    exact ((hu (owner S H R i.val.val) i).mpr rfl).symm
  obtain ⟨g,hg,hq⟩ := residual_joint_lifting S H R source target q q hReal
    (fun i j => GroupActions.orbital_nonempty _ _) hCover
  have hfix : ∀ q ∈ B, g • q = q := fun q hq' => hq ⟨q,hq'⟩
  refine ⟨restrictMotion S H R B g hfix,?_⟩
  intro a
  apply Subtype.ext
  exact hg a

/-- Finite actual named induced embeddings, with every literal fine
colour retained. -/
structure NamedEmbedding (B : Finset (Owner S H R))
    (A L : Finset (NamedCarrier S H R B)) where
  toEmbedding : ↥A ↪ ↥L
  owner : ∀ x, owner S H R (toEmbedding x).val.val = owner S H R x.val.val
  colours : ∀ x y, col S (toEmbedding x).val.val (toEmbedding y).val.val =
    col S x.val.val y.val.val

/-- Finite named embeddings extend to the actual full named group. -/
theorem named_embedding_extends (B : Finset (Owner S H R))
    (A L : Finset (NamedCarrier S H R B)) (e : NamedEmbedding S H R B A L) :
    ∃ f : NamedAut S H R B, ∀ a, f.val a.val = (e.toEmbedding a).val := by
  apply named_homogeneous S H R B A (fun a => (e.toEmbedding a).val)
  · exact Subtype.val_injective.comp e.toEmbedding.injective
  · intro q a
    change owner S H R (e.toEmbedding a).val.val = q ↔ owner S H R a.val.val = q
    rw [e.owner]
  · intro c a b
    change col S (e.toEmbedding a).val.val (e.toEmbedding b).val.val = c ↔
      col S a.val.val b.val.val = c
    rw [e.colours]

end
end CCO.OwnerTransversal
