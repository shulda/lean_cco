import CCO.TypedOrbitFrames.OrbitDiagram
import CCO.TypedOrbitFrames.OrbitCloneCycles
import CCO.StrongExact.PrescribedBaseGeneral
import CCO.RawExact.DiagramReindex

/-!
# Source11 T02: actual old orbit-diagram completion over the whole real base

The local triangle instances and long clone cycles are proved for the
literal diagram. The fixed-diagram chord induction supplies all cycles.
The accepted prescribed-base theorem then invokes old semantic CCO ONCE
and aligns the entire old base by ONE original automorphism.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse CCO.ParityHasse.Original CCO.RealClosure.Bounds

universe u v w z t r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} {Y : Type t} [Finite B] [Finite Y]
variable (base : B ↪ Sigma X) {i : ι} (q : X i)
variable (K : SimpleGraph Y) (e : S.Atom i i)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_no_short_cycles_no_triangle {g : Nat}
    (hg : 3 ≤ g) (hK : NoShortCycles K g) :
    ∀ x y z : Y, K.Adj x y → K.Adj y z → ¬ K.Adj x z := by
  intro x y z hxy hyz hxz
  have hnxy : x ≠ y := hxy.ne
  have hnyz : y ≠ z := hyz.ne
  have hnxz : x ≠ z := hxz.ne
  let f : Fin 3 ↪ Y := {
    toFun := fun p => if p = 0 then x else if p = 1 then y else z
    inj' := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all }
  apply hK 3 (by decide) hg f
  intro p
  fin_cases p
  · exact hxy
  · exact hyz
  · exact hxz.symm

/-- A clone-only specified cycle is LITERALLY a simple graph cycle,
with its original finite positions and no invented graph edges. -/
theorem original_orbit_clone_cycle_graph
    (C : SimpleCycle (originalOrbitDiagram S base q K e))
    (hClone : ∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y) :
    ∃ f : Fin C.length ↪ Y,
      (∀ p, C.vertices p = Sum.inr (f p)) ∧
      ∀ p, K.Adj (f p) (f (cyclicNext C.length_pos p)) := by
  choose y hy using hClone
  let f : Fin C.length ↪ Y := {
    toFun := y
    inj' := by
      intro p q hpq
      apply C.vertices.injective
      exact (hy p).trans ((congrArg Sum.inr hpq).trans (hy q).symm) }
  refine ⟨f,hy,?_⟩
  intro p
  obtain ⟨a,ha⟩ := C.specified p
  exact (original_orbit_clone_edge_reading S base q K e
    (hy p) (hy (cyclicNext C.length_pos p)) (C.next_ne p) a ha).1

/-- The actual source pure-power threshold discharges the clone-cycle
test for this one concrete orbit diagram. -/
theorem original_orbit_clone_cycle_hom
    {N : ℕ+}
    (hN : ∀ ℓ : Nat, N.val + 1 ≤ ℓ → CyclicWalk (atomGraph S e) ℓ)
    (hK : NoShortCycles K (max 3 (N.val + 1)))
    (C : SimpleCycle (originalOrbitDiagram S base q K e))
    (hClone : ∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y) :
    CycleHom C := by
  obtain ⟨f,hf,hEdges⟩ := original_orbit_clone_cycle_graph S base q K e C hClone
  have hLong : N.val + 1 ≤ C.length := by
    by_contra hn
    have hle : C.length ≤ max 3 (N.val + 1) := by omega
    exact hK C.length C.length_ge_three hle f hEdges
  apply original_monochromatic_cycle_hom_of_cyclic_walk S C e
  · intro p
    rw [hf p]
    rfl
  · intro p a ha
    exact (original_orbit_clone_edge_reading S base q K e
      (hf p) (hf (cyclicNext C.length_pos p)) (C.next_ne p) a ha).2
  · exact hN C.length hLong

/-- Source11's whole finite old graph is completed over the ACTUAL whole
real base. All local cycle providers are discharged; only the explicit
source fork atom and source high-girth graph are inputs. -/
theorem original_orbit_diagram_completion_threshold
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S) (nr2 : SortNR2 S i)
    (hq : (⟨i,q⟩ : Sigma X) ∉ Set.range base)
    (hfork : OriginalOrbitForks S base q e) :
    ∃ N : ℕ+, ∀ {Y : Type t} [Finite Y] (K : SimpleGraph Y),
      NoShortCycles K (max 3 (N.val + 1)) →
      ∃ f : DiagramHom (originalOrbitDiagram S base q K e),
        ∀ d : B, f.point (.inl d) = (base d).2 := by
  obtain ⟨N,hN⟩ := original_same_sort_pure_power_cycle_threshold S H sap nr2 e
  refine ⟨N,?_⟩
  intro Y _ K hK
  let D := originalOrbitDiagram S base q K e
  have hBase := original_orbit_complete_base_spokes S base q K e hq
  have hCycles : ∀ C : SimpleCycle D, CycleHom C := by
    apply original_complete_base_cycle_hom_of_local_tests S H sap D hBase
    · intro C h3 _
      apply original_triangle_cycle_hom_of_triangle S D C h3
      exact original_orbit_triangles S base q K e hfork
        (original_no_short_cycles_no_triangle K (le_max_left _ _) hK)
    · intro C _ hClone
      exact original_orbit_clone_cycle_hom S base q K e hN hK C hClone
  obtain ⟨f,_,hf⟩ :=
    PartialDiagram.strongCompletion_prescribed_base_any_universe_of_SAP_CCO H sap
      (semanticCCO_change_universe S cco) D (Set.range Sum.inl)
      (by
        rintro x ⟨d,rfl⟩ y ⟨b,rfl⟩ hxy
        exact hBase d (.inl b) hxy)
      (originalOrbitTarget base q) (by
        rintro x ⟨d,rfl⟩ y ⟨b,rfl⟩ hxy a ha
        exact ha) hCycles
  exact ⟨f,fun d => hf (.inl d) ⟨d,rfl⟩⟩

end CCO.TypedOrbitFrames
