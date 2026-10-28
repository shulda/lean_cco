import CCO.RawExact.JointCountableBackAndForth
import CCO.RawExact.JointFiniteExtension

universe u v w z q t

namespace CCO.RawExact

namespace JointBackAndForth

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type q}
variable [∀ k, MulAction G (Q k)]

noncomputable def graphOfFiniteMap (f : FiniteJointPartialIso G Q) : Graph G Q := by
  classical
  let row : Sigma Q → Row Q := fun p => ⟨p.1, p.2, f.send p⟩
  refine ⟨f.domain.image row, ?_⟩
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
  exact f.preserves p' q' hp' hq'

theorem row_mem_graphOfFiniteMap (f : FiniteJointPartialIso G Q)
    (p : Sigma Q) (hp : p ∈ f.domain) :
    (⟨p.1, p.2, f.send p⟩ : Row Q) ∈ (graphOfFiniteMap f).val := by
  classical
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

end JointBackAndForth

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Countable back-and-forth extends an actual finite joint partial
isomorphism to actual sortwise bijections. These bijections need not
be elements of the arbitrary finite-orbit witness group G. -/
theorem countable_joint_extension_of_exact_ball_helly
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]
    [Countable (Sigma Q)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (f : FiniteJointPartialIso G Q) :
    ∃ e : ∀ k, Q k ≃ Q k,
      (∀ (k l : K) (a : Q k) (b : Q l),
        GroupActions.orbital (G := G) a b (e k a) (e l b)) ∧
      (∀ p ∈ f.domain, e p.1 p.2 = f.send p) := by
  have hExt : JointBackAndForth.ExtensionProperty (G := G) (Q := Q) :=
    JointBackAndForth.graph_one_point_extension S H hHelly Q root π ontoπ equivπ E hE
  obtain ⟨e, hePair, heStart⟩ :=
    JointBackAndForth.countable_joint_orbital_automorphism hExt
      (JointBackAndForth.graphOfFiniteMap f)
  refine ⟨e, hePair, ?_⟩
  intro p hp
  exact heStart _ (JointBackAndForth.row_mem_graphOfFiniteMap f p hp)

end CCO.RawExact
