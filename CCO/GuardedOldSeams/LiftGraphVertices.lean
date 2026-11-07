import CCO.StrongExact.ThetaBranchInjective
import CCO.GuardedTwoRoot.UniformTheta

/-!
# Finite old roots with separately tagged private word interiors

Different local theta packages have different unordered root pairs.
Consequently two local packages can share at most one formal vertex.
This is only the literal finite vertex construction; no completion or
new mathematical existence premise is asserted here.
-/

universe u v a p q

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

structure RootWordSystem (P : Type p) (K : Type q) [Finite P] [Finite K] where
  sort : P → ι
  left : K → P
  right : K → P
  left_ne_right : ∀ k, left k ≠ right k
  unordered_unique : ∀ k l,
    ({left k, right k} : Set P) = {left l, right l} → k = l
  words : ∀ k, List (PositiveWord S (sort (left k)) (sort (right k)))

namespace RootWordSystem

variable {S} {P : Type p} {K : Type q} [Finite P] [Finite K]
variable (R : RootWordSystem S P K)

def Vertex : Type (max p q) :=
  P ⊕ (Σ k : K, Σ b : Fin (R.words k).length,
    wordInterior S ((R.words k).get b))

instance finite_vertex : Finite R.Vertex := by
  classical
  letI (k : K) (b : Fin (R.words k).length) :
      Finite (wordInterior S ((R.words k).get b)) :=
    finite_wordInterior S ((R.words k).get b)
  change Finite (P ⊕ (Σ k : K, Σ b : Fin (R.words k).length,
    wordInterior S ((R.words k).get b)))
  infer_instance

/-- The actual union has one copy of every old root and precisely the
strict interiors of the specified original words.  Singleton words
contribute zero vertices. -/
theorem vertex_card [Fintype K] :
    Nat.card R.Vertex = Nat.card P +
      ∑ k : K, ∑ b : Fin (R.words k).length,
        (GuardedTwoRoot.TypedPrefix.length S ((R.words k).get b) - 1) := by
  classical
  letI (k : K) (b : Fin (R.words k).length) :
      Finite (wordInterior S ((R.words k).get b)) :=
    finite_wordInterior S ((R.words k).get b)
  change Nat.card (P ⊕ (Σ k : K, Σ b : Fin (R.words k).length,
    wordInterior S ((R.words k).get b))) = _
  rw [Nat.card_sum, Nat.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_sigma]
  simp only [GuardedTwoRoot.word_interior_card]

/-- Equivalent package accounting: each local theta contributes its
actual size minus its two already counted old roots. -/
theorem vertex_card_theta [Fintype K] :
    Nat.card R.Vertex = Nat.card P +
      ∑ k : K, (Nat.card (thetaVertices S (R.words k)) - 2) := by
  rw [R.vertex_card]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [GuardedTwoRoot.theta_vertices_card]
  simp

def vertexSort : R.Vertex → ι
  | .inl p => R.sort p
  | .inr ⟨k, b, z⟩ => wordPositionSort S ((R.words k).get b) z.val

/-- A local theta package uses the old roots literally and tags every
private interior with its package and its original word index. -/
def embed (k : K) : thetaVertices S (R.words k) → R.Vertex
  | .inl false => .inl (R.left k)
  | .inl true => .inl (R.right k)
  | .inr ⟨b, z⟩ => .inr ⟨k, b, z⟩

theorem embed_sort (k : K) (z : thetaVertices S (R.words k)) :
    R.vertexSort (R.embed k z) = thetaVertexSort S (R.words k) z := by
  cases z with
  | inl b => cases b <;> rfl
  | inr z => rfl

@[simp] theorem embed_left (k : K) :
    R.embed k (thetaLeft S (R.words k)) = .inl (R.left k) := rfl

@[simp] theorem embed_right (k : K) :
    R.embed k (thetaRight S (R.words k)) = .inl (R.right k) := rfl

theorem embed_injective (k : K) : Function.Injective (R.embed k) := by
  intro z t h
  cases z with
  | inl b =>
      cases t with
      | inl c =>
          cases b <;> cases c
          · rfl
          · exact False.elim (R.left_ne_right k (Sum.inl.inj h))
          · exact False.elim (R.left_ne_right k (Sum.inl.inj h).symm)
          · rfl
      | inr t => cases b <;> cases h
  | inr z =>
      cases t with
      | inl b => cases b <;> cases h
      | inr t =>
          apply congrArg Sum.inr
          have he : (⟨k, z⟩ : Σ k : K, Σ b : Fin (R.words k).length,
              wordInterior S ((R.words k).get b)) = ⟨k, t⟩ := Sum.inr.inj h
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using he

private theorem roots_of_cross_embed_eq {k l : K} (hkl : k ≠ l)
    (z : thetaVertices S (R.words k)) (t : thetaVertices S (R.words l))
    (h : R.embed k z = R.embed l t) :
    ∃ b c : Bool, z = .inl b ∧ t = .inl c := by
  cases z with
  | inl b =>
      cases t with
      | inl c => exact ⟨b, c, rfl, rfl⟩
      | inr t => cases b <;> cases h
  | inr z =>
      cases t with
      | inl c => cases c <;> cases h
      | inr t =>
          have he : (⟨k, z⟩ : Σ k : K, Σ b : Fin (R.words k).length,
              wordInterior S ((R.words k).get b)) = ⟨l, t⟩ := Sum.inr.inj h
          exact False.elim (hkl (congrArg Sigma.fst he))

private theorem root_pair_unique (k l : K) (b c : Bool)
    (hbc : b ≠ c)
    (hleft : R.embed k (.inl false) = R.embed l (.inl b))
    (hright : R.embed k (.inl true) = R.embed l (.inl c)) : k = l := by
  apply R.unordered_unique k l
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · have hL : R.left k = R.left l := Sum.inl.inj hleft
    have hR : R.right k = R.right l := Sum.inl.inj hright
    rw [hL, hR]
  · have hL : R.left k = R.right l := Sum.inl.inj hleft
    have hR : R.right k = R.left l := Sum.inl.inj hright
    rw [hL, hR]
    exact Set.pair_comm _ _
  · exact False.elim (hbc rfl)

/-- Two different packages cannot contain the same pair of distinct
formal vertices.  This is the edge-uniqueness interface for literal
gluing of their single-valued original-colour diagrams. -/
theorem embed_overlap_unique (k l : K)
    (z t : thetaVertices S (R.words k))
    (z' t' : thetaVertices S (R.words l))
    (hne : z ≠ t) (hz : R.embed k z = R.embed l z')
    (ht : R.embed k t = R.embed l t') : k = l := by
  classical
  by_contra hkl
  obtain ⟨b, b', rfl, rfl⟩ := R.roots_of_cross_embed_eq hkl z z' hz
  obtain ⟨c, c', rfl, rfl⟩ := R.roots_of_cross_embed_eq hkl t t' ht
  have hbc : b ≠ c := fun h => hne (congrArg Sum.inl h)
  have hbc' : b' ≠ c' := by
    intro h
    have he := hz.trans ((congrArg (R.embed l) (congrArg Sum.inl h)).trans ht.symm)
    exact hne (R.embed_injective k he)
  apply hkl
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · exact R.root_pair_unique k l b' c' hbc' hz ht
  · exact R.root_pair_unique k l c' b' hbc'.symm ht hz
  · exact False.elim (hbc rfl)

noncomputable def branchPosition (k : K) (b : Fin (R.words k).length)
    (z : wordPositions S ((R.words k).get b)) : R.Vertex :=
  R.embed k (thetaBranchPosition S (R.words k) b z)

theorem branchPosition_sort (k : K) (b : Fin (R.words k).length)
    (z : wordPositions S ((R.words k).get b)) :
    R.vertexSort (R.branchPosition k b z) =
      wordPositionSort S ((R.words k).get b) z :=
  (R.embed_sort k _).trans (thetaBranchPosition_sort S (R.words k) b z)

theorem branchPosition_injective (k : K) (b : Fin (R.words k).length) :
    Function.Injective (R.branchPosition k b) :=
  (R.embed_injective k).comp (thetaBranchPosition_injective S (R.words k) b)

@[simp] theorem branchPosition_source (k : K) (b : Fin (R.words k).length) :
    R.branchPosition k b (wordSource S ((R.words k).get b)) =
      .inl (R.left k) := by
  unfold branchPosition
  rw [thetaBranchPosition_source]
  rfl

@[simp] theorem branchPosition_target (k : K) (b : Fin (R.words k).length) :
    R.branchPosition k b (wordTarget S ((R.words k).get b)) =
      .inl (R.right k) := by
  unfold branchPosition
  rw [thetaBranchPosition_target]
  rfl

end RootWordSystem
end CCO.GuardedOldSeams
