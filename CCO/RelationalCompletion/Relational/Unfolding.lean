import CCO.RelationalCompletion.Relational.Profiles
import CCO.RelationalCompletion.Collision.Counting
import Mathlib.Data.Set.Finite.Range

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V W : Type v}

/-- C14: concrete finite descent of the actual collision-pair count.
No completion, clone or injectivization provider is assumed. Protected sets
may form ANY family; only their old restrictions must be injective. -/
theorem collision_unfolding (A : Structure L V) (U : Structure L W) [Finite V]
    (hom : U.Homogeneous) (sap : U.AgeSAP) (h : V → W) (hh : A.IsHE U h)
    {ι : Type*} (S : ι → Set V) (hinj : ∀ i, Set.InjOn h (S i)) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      ∀ i, U.SameImageType h k (S i) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  suffices ht : ∀ n (h : V → W), Collision.collisionCount h = n →
      A.IsHE U h → (∀ i, Set.InjOn h (S i)) →
      ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
        ∀ i, U.SameImageType h k (S i) from ht _ h rfl hh hinj
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h hn hh hi
    by_cases hj : Function.Injective h
    · exact ⟨h, hh, hj, fun _ => SameImageType.refl⟩
    · obtain ⟨x, y, hxy, he⟩ : ∃ x y, x ≠ y ∧ h x = h y := by
        simp only [Function.Injective, not_forall] at hj
        obtain ⟨x, y, he, hne⟩ := hj
        exact ⟨x, y, hne, he⟩
      let : Finite (Set.range h) := by infer_instance
      let v : Set.range h := ⟨h x, ⟨x, rfl⟩⟩
      obtain ⟨e, hfix, hfresh⟩ := U.exists_induced_clone hom sap (Set.range h) v
      let k := split h {x} (e.point v)
      have ht : ∀ z ∈ ({x} : Set V), h z = v.val := by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        rfl
      have hk : A.IsHE U k := hh.split {x} v ht e hfix
      have hki : ∀ i, Set.InjOn k (S i) :=
        fun i => split_injOn U h {x} (S i) v ht (hi i) e hfix
      have hkt : ∀ i, U.SameImageType h k (S i) :=
        fun i => split_sameImageType U h {x} (S i) v ht (hi i) e hfix
      have hkdef : k = Collision.splitMap h {x} (e.point v) := rfl
      have hlt : Collision.collisionCount k < n := by
        rw [hkdef, ← hn]
        exact Collision.collisionCount_split_singleton_lt h x y (e.point v) hxy he hfresh
      obtain ⟨l, hl, hli, hlt⟩ := ih _ hlt k rfl hk hki
      exact ⟨l, hl, hli, fun i => SameImageType.trans (hkt i) (hlt i)⟩

end CCO.RelationalCompletion.Relational.Structure
