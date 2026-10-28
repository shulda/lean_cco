import CCO.DiagramNeighbours
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.EquivFin

/-!
# SAP injectivization of finite partial diversity-diagram homomorphisms

The finite induction never supposes that the current images of neighbours
are distinct. At each step the moving vertex is sent outside the ENTIRE
current image, preserving the old images of all other formal vertices.
The induction fixes a designated set on which the input was already
injective and avoids any finite forbidden set on all unpinned vertices.

This result uses only actual age-SAP and original finite homogeneity;
there is no homomorphic CCO, NR2, RAW Helly or selector hypothesis.
-/

universe u v w

namespace CCO.DiagramHom

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X} {V : Type w}
variable {D : PartialDiagram S V}
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Induction invariant: pinned real images stay literal, and every
processed formal vertex has a fresh image against ALL other vertices
and avoids the finite forbidden set. -/
private def Processed (S₀ : Set V) (f₀ f : DiagramHom D)
    (Z : Set (Sigma X)) (T : Finset V) : Prop :=
  (∀ s ∈ S₀, f.image s = f₀.image s) ∧
  ∀ u ∈ T,
    f.image u ∉ Z ∧
    ∀ v : V, u ≠ v → f.image u ≠ f.image v

private theorem process_finset_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f₀ : DiagramHom D) (S₀ : Set V)
    (Z : Set (Sigma X)) (hZ : Z.Finite)
    (T : Finset V) (hTS : ∀ u ∈ T, u ∉ S₀) :
    ∃ f : DiagramHom D, Processed S₀ f₀ f Z T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨f₀, ?_⟩
      constructor
      · intro s hs
        rfl
      · intro u hu
        simp at hu
  | @insert x T hnot ih =>
      have hTS' : ∀ u ∈ T, u ∉ S₀ := by
        intro u hu
        exact hTS u (Finset.mem_insert_of_mem hu)
      obtain ⟨f, hPin, hDone⟩ := ih hTS'
      have hxS : x ∉ S₀ := hTS x (Finset.mem_insert_self x T)
      obtain ⟨f', hNew, hOld⟩ :=
        fresh_move_one_of_SAP H sap f x Z hZ
      refine ⟨f', ?_, ?_⟩
      · intro s hs
        have hsx : s ≠ x := by
          intro h
          subst s
          exact hxS hs
        calc
          f'.image s = f.image s := hOld s hsx
          _ = f₀.image s := hPin s hs
      · intro u hu
        rcases Finset.mem_insert.mp hu with hux | huT
        · subst u
          constructor
          · intro hxZ
            exact hNew (Or.inl hxZ)
          · intro v hxv heq
            have hvx : v ≠ x := Ne.symm hxv
            have hfv := hOld v hvx
            have hInRange : f'.image x ∈ Set.range f.image := by
              refine ⟨v, ?_⟩
              exact (heq.trans hfv).symm
            exact hNew (Or.inr hInRange)
        · obtain ⟨huZ, huUnique⟩ := hDone u huT
          have hux : u ≠ x := by
            intro hux
            subst u
            exact hnot huT
          have hfu := hOld u hux
          constructor
          · rw [hfu]
            exact huZ
          · intro v huv heq
            by_cases hvx : v = x
            · subst v
              have hInRange : f'.image x ∈ Set.range f.image := by
                refine ⟨u, ?_⟩
                exact hfu.symm.trans heq
              exact hNew (Or.inr hInRange)
            · have hfv := hOld v hvx
              have hEq : f.image u = f.image v := by
                calc
                  f.image u = f'.image u := hfu.symm
                  _ = f'.image v := heq
                  _ = f.image v := hfv
              exact huUnique v huv hEq

/-- STRONG C05: every finite specified diversity homomorphism can be made
injective, fixing an arbitrary already-injective designated vertex set
and avoiding a finite forbidden set on every unpinned vertex. -/
theorem injectivize_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f₀ : DiagramHom D) (S₀ : Set V)
    (hPin : ∀ u ∈ S₀, ∀ v ∈ S₀, f₀.image u = f₀.image v → u = v)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ f : DiagramHom D,
      f.IsInjective ∧
      (∀ s ∈ S₀, f.image s = f₀.image s) ∧
      (∀ u ∉ S₀, f.image u ∉ Z) := by
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite V
  let T : Finset V := Finset.univ.filter (fun v => v ∉ S₀)
  have hTS : ∀ u ∈ T, u ∉ S₀ := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  obtain ⟨f, hFixed, hDone⟩ :=
    process_finset_of_SAP H sap f₀ S₀ Z hZ T hTS
  refine ⟨f, ?_, hFixed, ?_⟩
  · intro u v hEq
    by_cases hu : u ∈ S₀
    · by_cases hv : v ∈ S₀
      · apply hPin u hu v hv
        calc
          f₀.image u = f.image u := (hFixed u hu).symm
          _ = f.image v := hEq
          _ = f₀.image v := hFixed v hv
      · have hvT : v ∈ T := by
          simp [T, hv]
        have hvu : v ≠ u := by
          intro heq
          subst v
          exact hv hu
        exact False.elim ((hDone v hvT).2 u hvu hEq.symm)
    · have huT : u ∈ T := by
        simp [T, hu]
      by_contra huv
      have huv' : u ≠ v := huv
      exact (hDone u huT).2 v huv' hEq
  · intro u hu
    have huT : u ∈ T := by simp [T, hu]
    exact (hDone u huT).1

end CCO.DiagramHom
