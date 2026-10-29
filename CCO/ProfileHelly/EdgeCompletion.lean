import CCO.ProfileHelly.Fill
import Mathlib.Data.Set.Finite.Range
import CCO.ProfileHelly.PathIntersections

/-! Positive-profile Helly chooses an actual common atom for ALL current
simple paths. Empty path families use the nonempty endpoint palette. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)

noncomputable def pathProfiles [Finite V] {x y : V} (hxy : x ≠ y) :
    Finset (T.Menu (sort x) (sort y)) := by
  classical
  let : Finite (D.graph.Path x y) := D.simple_paths_finite x y
  exact (Set.finite_range (fun p : D.graph.Path x y => D.pathProfile hxy p)).toFinset

@[simp] theorem mem_pathProfiles [Finite V] {x y : V} (hxy : x ≠ y)
    (A : T.Menu (sort x) (sort y)) :
    A ∈ D.pathProfiles hxy ↔ ∃ p : D.graph.Path x y, D.pathProfile hxy p = A := by
  classical
  simp [pathProfiles]

/-- C16/C17: one colour works for EVERY old simple path. No zero-word
profile or Helly premise on an empty family is introduced. -/
theorem common_path_colour [Finite V] (laws : TableLaws T) (helly : Word.Helly (T := T))
    (alg : D.Algebraic) (x y : V) (hxy : x ≠ y) :
    ∃ a : T.Atom (sort x) (sort y), ∀ p : D.graph.Path x y, a ∈ D.pathProfile hxy p := by
  classical
  let F := D.pathProfiles hxy
  by_cases hF : F.Nonempty
  · have words : ∀ A ∈ F, ∃ w : Word T (sort x) (sort y), w.profile = A := by
      intro A hA
      obtain ⟨p,rfl⟩ := (D.mem_pathProfiles hxy A).mp hA
      exact ⟨D.walkWord p.val (SimpleGraph.Walk.not_nil_of_ne hxy),rfl⟩
    have pairs : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty := by
      intro A hA B hB
      obtain ⟨p,rfl⟩ := (D.mem_pathProfiles hxy A).mp hA
      obtain ⟨q,rfl⟩ := (D.mem_pathProfiles hxy B).mp hB
      exact D.path_profiles_intersect laws alg x y hxy p q
    obtain ⟨a,ha⟩ := helly (sort x) (sort y) F hF words pairs
    refine ⟨a,fun p => ?_⟩
    exact Set.mem_iInter₂.mp ha _ ((D.mem_pathProfiles hxy _).mpr ⟨p,rfl⟩)
  · obtain ⟨a⟩ := T.nonemptyAtom (sort x) (sort y)
    refine ⟨a,fun p => ?_⟩
    exact False.elim (hF ⟨D.pathProfile hxy p,(D.mem_pathProfiles hxy _).mpr ⟨p,rfl⟩⟩)

end CCO.ProfileHelly.Network
