import CCO.RankInduction.Basis

/-! Singleton unsafe transports prove vertex transitivity of the SAME
closed rooted witness. No independent closure or enlargement is taken. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact Owners.Product Owners.Provider

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def VertexTransitive (W : Set M) : Prop :=
  ∀ x y : W, ∃ α : OrbitalAut G M (Subtype.val : W → M), α.val x = y

include H in
theorem witness_vertex_transitive (safe : Set (S.Atom () ()))
    (A0 W : Set M) (w : Witness S G safe A0 W) : VertexTransitive (G := G) W := by
  classical
  intro x y
  obtain ⟨αx,-,hx⟩ := w.roots {x} (FiniteLift.unsafe_singleton _ x) x (Set.mem_singleton x)
  obtain ⟨αy,-,hy⟩ := w.roots {y} (FiniteLift.unsafe_singleton _ y) y (Set.mem_singleton y)
  let a := αx.val x
  let b := αy.val y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () a.val b.val
  let p : OrbitalPartial (G := G) (Subtype.val : W → M) := {
    domain := {a}
    map := fun _ => b
    injective := by
      intro u v _
      exact Subtype.ext ((Set.mem_singleton_iff.mp u.property).trans
        (Set.mem_singleton_iff.mp v.property).symm)
    pair := by
      intro u v
      have hu : u.val = a := Set.mem_singleton_iff.mp u.property
      have hv : v.val = a := Set.mem_singleton_iff.mp v.property
      exact ⟨g,by rw [hu]; exact hg,by rw [hv]; exact hg⟩ }
  have dom : p.domain ⊆ {z | z.val ∈ A0} := by
    intro z hz
    have he : z = a := Set.mem_singleton_iff.mp hz
    exact he ▸ hx
  have ran : ∀ z, p.map z ∈ {z | z.val ∈ A0} := fun _ => hy
  obtain ⟨β,hβ⟩ := w.extensions p dom ran
  have hab : β.val a = b := hβ ⟨a,Set.mem_singleton a⟩
  refine ⟨αy⁻¹ * β * αx,?_⟩
  change αy.val.symm (β.val (αx.val x)) = y
  rw [hab]
  exact αy.val.symm_apply_apply y

include H in
theorem closed_transitive_same_witness (safe : Set (S.Atom () ()))
    (A0 W : Set M) (w : Witness S G safe A0 W)
    (closedW : FiniteLift.aclSet G W = W) :
    Witness S G safe A0 W ∧ FiniteLift.aclSet G W = W ∧ VertexTransitive (G := G) W :=
  ⟨w,closedW,witness_vertex_transitive S H safe A0 W w⟩

end
end CCO.RankInduction
