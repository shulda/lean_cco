import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.ParityHasse.Original.CycleTemplates
import CCO.ParityHasse.Sparse.ConnectedExtraction
import Mathlib.Data.Fintype.EquivFin

/-! The original CCO/high-chromatic contradiction. The sparse construction
is supplied by the separately proved finite combinatorial theorem; no
SAP, countability, exactness or injectivity of the CCO map occurs here. -/
universe u v w t
namespace CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The actual graph of one original symmetric diversity orbital. -/
def atomGraph (c : S.Atom i i) : SimpleGraph (X i) where
  Adj := S.atomRel c
  symm := ⟨by
    intro x y h
    simpa only [AtomicSource.atomRel, S.symmetricLoop] using (S.colour_swap x y c).mp h⟩
  loopless := ⟨fun x h => S.atomRel_ne h rfl⟩

noncomputable def monochromaticDiagram {V : Type*} [Finite V]
    (K : SimpleGraph V) (c : S.Atom i i) : PartialDiagram S V := by
  classical
  exact
    { finite_type := inferInstance
      vertexSort := fun _ => i
      edge := fun x y _ => if K.Adj x y then some c else none
      edge_reverse := by
        intro x y _ a
        by_cases hxy : K.Adj x y <;>
          simp [hxy, K.adj_comm, S.symmetricLoop] }

theorem monochromaticDiagram_edge_iff {V : Type*} [Finite V]
    (K : SimpleGraph V) (c : S.Atom i i) {x y : V} (hxy : x ≠ y)
    (a : S.Atom i i) :
    (monochromaticDiagram S K c).edge x y hxy = some a ↔ K.Adj x y ∧ c = a := by
  classical
  by_cases h : K.Adj x y <;> simp [monochromaticDiagram, h]

/-- C09 templates give every actual specified cycle a homomorphism. -/
theorem monochromatic_cycles_map {V : Type*} [Finite V]
    (K : SimpleGraph V) (c : S.Atom i i) {x y : X i}
    (p : (atomGraph S c).Walk x x) (hc : S.atomRel c x y)
    (hp : Odd p.length) (hg : Sparse.NoShortCycles K p.length) :
    ∀ C : SimpleCycle (monochromaticDiagram S K c), CycleHom C := by
  intro C
  have hAdj (j : Fin C.length) : K.Adj (C.vertices j)
      (C.vertices (cyclicNext C.length_pos j)) := by
    obtain ⟨a, ha⟩ := C.specified j
    exact ((monochromaticDiagram_edge_iff S K c (C.next_ne j) a).mp ha).1
  have hlarge : p.length < C.length := by
    by_contra h
    exact hg C.length C.length_ge_three (by omega) C.vertices hAdj
  obtain ⟨hn, f, hf⟩ := cyclicWalk_even_or_odd_above p hc hp C.length_pos hlarge
  refine ⟨f, ?_⟩
  intro j a ha
  have hca := ((monochromaticDiagram_edge_iff S K c (C.next_ne j) a).mp ha).2
  subst a
  exact hf j

/-- Walks of the finite graph keep any CCO image inside one actual F-class. -/
theorem homogeneous_image_one_class {V : Type*} (K : SimpleGraph V)
    (F : Setoid (X i)) (f : V → X i)
    (hf : ∀ x y, K.Adj x y → F (f x) (f y)) {x y : V}
    (hxy : K.Reachable x y) : F (f x) (f y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact F.refl _
  | @cons a b c hab p ih => exact F.trans (hf a b hab) ih

/-- The source contradiction from the independently constructed finite
sparse-graph theorem. Final source wrapper discharges `sparse` concretely. -/
theorem no_odd_orbital_walk_from_sparse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (sparse : ∀ q g : Nat, 0 < q → 0 < g →
      Nonempty (Sparse.ConnectedHighGirthChromatic q g))
    (E F : ColourEq S i) (a : X i)
    [Finite (RelativeClass E.val F.val a)]
    (c : S.Atom i i)
    (hFE : ∀ x y, S.atomRel c x y → F x y ∧ ¬ E x y) :
    ∀ x (p : (atomGraph S c).Walk x x), ¬ Odd p.length := by
  intro x p hp
  classical
  let Q := RelativeClass E.val F.val a
  letI : Nonempty Q := ⟨Quotient.mk _ ⟨a, F.val.refl a⟩⟩
  letI : Fintype Q := Fintype.ofFinite Q
  let q := Nat.card Q
  have hq : 0 < q := Nat.card_pos
  have hp0 : 0 < p.length := by have ho := Nat.odd_iff.mp hp; omega
  obtain ⟨W⟩ := sparse q p.length hq hp0
  obtain ⟨x₀, y₀, hc₀⟩ := S.realized c
  have hc : ∃ y, S.atomRel c x y :=
    invariant_nonempty_serial S H
      (fun b d b' d' hcol => by change S.colour b d = some c ↔ S.colour b' d' = some c; rw [hcol])
      ⟨x₀, y₀, hc₀⟩ x
  obtain ⟨y, hxy⟩ := hc
  let D := monochromaticDiagram S W.graph c
  obtain ⟨f⟩ := cco (Fin W.size) D
    (monochromatic_cycles_map S W.graph c p hxy hp W.noShortCycles)
  let root : Fin W.size := Classical.choice W.connected.nonempty
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H i (f.point root) a
  let point : Fin W.size → X i := fun v => g • f.point v
  have edge (s t : Fin W.size) (hst : W.graph.Adj s t) :
      S.atomRel c (point s) (point t) := by
    have hne : s ≠ t := W.graph.ne_of_adj hst
    have hcol := f.preserves_edge s t hne c
      ((monochromaticDiagram_edge_iff S W.graph c hne c).mpr ⟨hst, rfl⟩)
    change S.colour (g • f.point s) (g • f.point t) = some c
    rw [S.colourInvariant_of_homogeneous H]
    exact hcol
  have inF (v : Fin W.size) : F a (point v) := by
    have hf := homogeneous_image_one_class W.graph F.val point
      (fun s t hst => (hFE _ _ (edge s t hst)).1) (W.connected root v)
    have hroot : point root = a := hg
    change F (point root) (point v) at hf
    rw [hroot] at hf
    exact hf
  let e : Q ≃ Fin q := Fintype.equivFinOfCardEq (by simp [q, Nat.card_eq_fintype_card])
  let colour : Fin W.size → Fin q := fun v => e (Quotient.mk _ ⟨point v, inF v⟩)
  obtain ⟨s, t, hst, hcolour⟩ := W.monochromatic colour
  have he := Quotient.exact (e.injective hcolour)
  exact (hFE _ _ (edge s t hst)).2 he

end CCO.ParityHasse.Original
