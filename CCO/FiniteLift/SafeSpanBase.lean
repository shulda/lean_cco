import CCO.FiniteLift.ClosureOrbit
import CCO.FiniteLift.Palette

/-! Arbitrary finite closed spans, with their complete base embeddings.
All objects are actual induced subsets; no accidental overlap between
their chosen charts is identified in the input span. -/

universe v w t
namespace CCO.FiniteLift

structure OrbitalEmbedding (G : Type*) [Group G] {M : Type*} [MulAction G M]
    (C D : Set M) where
  toEmbedding : C ↪ D
  pair : ∀ x y : C, GroupActions.orbital (G := G) x.val y.val
    (toEmbedding x).val (toEmbedding y).val

/-- Strong closed amalgamation quantifies over BOTH arbitrary base maps.
The output amalgam is finite; it is not required to be closed. -/
def StrongClosedAmalgamation (G : Type*) [Group G] {M : Type*} [MulAction G M]
    (closure : Set M → Set M) (safe : M → M → Prop) : Prop :=
  ∀ (C L R : Set M), C.Finite → L.Finite → R.Finite →
    closure C = C → closure L = L → closure R = R →
    ∀ (f : OrbitalEmbedding G C L) (g : OrbitalEmbedding G C R),
    ∃ (W : Set M), W.Finite ∧
      ∃ (l : OrbitalEmbedding G L W) (r : OrbitalEmbedding G R W),
        (∀ c, l.toEmbedding (f.toEmbedding c) = r.toEmbedding (g.toEmbedding c)) ∧
        (∀ x y, l.toEmbedding x = r.toEmbedding y ↔
          ∃ c, f.toEmbedding c = x ∧ g.toEmbedding c = y) ∧
        (∀ x y, x ∉ Set.range f.toEmbedding → y ∉ Set.range g.toEmbedding →
          safe (l.toEmbedding x).val (r.toEmbedding y).val)

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]

/-- A whole finite fine embedding extends to one actual original group
element. This is a direct finite source-homogeneity application. -/
theorem real_embedding_lift (H : HomogeneousSource S G) {C D : Set A}
    (hC : C.Finite) (e : OrbitalEmbedding G C D) :
    ∃ g : G, ∀ x : C, g • x.val = (e.toEmbedding x).val := by
  letI : Finite C := hC.to_subtype
  have hc : ∀ x y : C,
      taggedColour S (⟨(), x.val⟩ : Sigma (fun _ : Unit => A)) ⟨(), y.val⟩ =
        taggedColour S ⟨(), (e.toEmbedding x).val⟩ ⟨(), (e.toEmbedding y).val⟩ := by
    intro x y
    obtain ⟨g, hx, hy⟩ := e.pair x y
    have hh := H.preserves_colours g ⟨(), x.val⟩ ⟨(), y.val⟩
    simpa only [Sigma.smul_mk, hx, hy] using hh.symm
  obtain ⟨g, hg⟩ := H.extends_finite_diagram
    (fun x : C => (⟨(), x.val⟩ : Sigma (fun _ : Unit => A)))
    (fun x : C => (⟨(), (e.toEmbedding x).val⟩ : Sigma (fun _ : Unit => A))) hc
  refine ⟨g, ?_⟩
  intro x
  simpa only [Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using hg x

namespace ExactKernel
variable {S} (K : ExactKernel S G)

/-- Lift an arbitrary quotient base embedding on the ENTIRE finite base,
then restrict that single lift to all real points above that base. -/
theorem fullPreimage_embedding [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    {C D : Set K.Q} (hC : C.Finite)
    (e : OrbitalEmbedding G C D) :
    ∃ f : OrbitalEmbedding G (K.proj ⁻¹' C) (K.proj ⁻¹' D),
      ∀ x, K.proj (f.toEmbedding x).val =
        (e.toEmbedding ⟨K.proj x.val, x.property⟩).val := by
  letI : Finite C := hC.to_subtype
  obtain ⟨g, hg⟩ := K.finite_embedding_lift H cco
    (fun x : C => x.val) (fun x => (e.toEmbedding x).val) e.pair
  have hmem (x : K.proj ⁻¹' C) : K.proj (g • x.val) ∈ D := by
    rw [K.proj_smul, hg ⟨K.proj x.val, x.property⟩]
    exact (e.toEmbedding ⟨K.proj x.val, x.property⟩).property
  refine ⟨⟨⟨fun x => ⟨g • x.val, hmem x⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x y h
    exact Subtype.ext ((MulAction.injective g) (congrArg Subtype.val h))
  · intro x y
    exact ⟨g, rfl, rfl⟩
  · intro x
    exact (K.proj_smul g x.val).trans (hg ⟨K.proj x.val, x.property⟩)

end ExactKernel
end CCO.FiniteLift
