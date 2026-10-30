import CCO.FiniteFibres.CycleWalks
import CCO.ParityHasse.Sparse.Existence

/-! C01--C08: finite symmetric CCO forces every atom graph to be bipartite.
The only mathematical package provider is the internal high-girth graph.
There is no homogeneity, transitivity, SAP or finite-unused-palette premise. -/

namespace CCO.FiniteFibres
open RelationalCompletion
variable {C : Type*} (T : Target C)

noncomputable def monochromaticDiagram {n : Nat} (K : SimpleGraph (Fin n)) (a : C) :
    Atomic.Diagram (palette C) n := by
  classical
  exact {
    tag := fun _ => ()
    edge := fun x y => if K.Adj x y then some a else none
    edge_self := by intro x; simp
    edge_reverse := by intro x y; simp only [palette,Option.map_id,id_eq,K.adj_comm]
    typed := fun _ _ _ _ => ⟨rfl,rfl⟩ }

theorem monochromatic_edge_iff {n : Nat} (K : SimpleGraph (Fin n)) (a b : C)
    (x y : Fin n) :
    (monochromaticDiagram K a).edge x y = some b ↔ K.Adj x y ∧ a = b := by
  classical
  change (if K.Adj x y then (some a : Option C) else none) = some b ↔ _
  by_cases h : K.Adj x y
  · rw [if_pos h]
    exact ⟨fun he => ⟨h,Option.some.inj he⟩,fun ⟨_,he⟩ => congrArg some he⟩
  · rw [if_neg h]
    constructor
    · intro he
      cases he
    · rintro ⟨he,_⟩
      exact (h he).elim

theorem monochromatic_cycles_map {n : Nat} (K : SimpleGraph (Fin n)) (a : C)
    {x y : Fin T.size} (p : (atomGraph T a).Walk x x)
    (hxy : (atomGraph T a).Adj x y) (hp : Odd p.length)
    (hg : ParityHasse.Sparse.NoShortCycles K p.length) :
    ∀ L : Atomic.SimpleCycle (monochromaticDiagram K a), Atomic.CycleHomInto L T := by
  intro L
  have hAdj (j : Fin L.length) : K.Adj (L.vertices j)
      (L.vertices (Atomic.cyclicNext (by have := L.length_ge_three; omega) j)) := by
    obtain ⟨b,hb⟩ := L.specified j
    exact ((monochromatic_edge_iff K a b _ _).mp hb).1
  have hlarge : p.length < L.length := by
    by_contra h
    exact hg L.length L.length_ge_three (by omega) L.vertices hAdj
  obtain ⟨hn,f,hf⟩ := cyclicWalk_even_or_odd_above p hxy hp
    (by have := L.length_ge_three; omega) hlarge
  refine ⟨f,fun _ => Subsingleton.elim (α := Unit) _ _,?_⟩
  intro j b hb
  have hab := ((monochromatic_edge_iff K a b _ _).mp hb).2
  subst b
  exact hf j

/-- Even an arbitrary odd CLOSED atom walk yields the sparse contradiction.
The simple odd cycle obstruction is a special case. -/
theorem no_odd_atom_walk (cco : SemanticCCO T) (a : C)
    (x : Fin T.size) (p : (atomGraph T a).Walk x x) : ¬ Odd p.length := by
  intro hp
  classical
  cases p with
  | nil => simpa using hp
  | @cons _ y _ hxy tail =>
    let p := tail.cons hxy
    have hq : 0 < T.size := by have := x.isLt; omega
    obtain ⟨W⟩ := ParityHasse.Sparse.high_girth_chromatic_exists hq p.length
    let D := monochromaticDiagram W.graph a
    obtain ⟨f⟩ := cco D (monochromatic_cycles_map T W.graph a p hxy hp W.noShortCycles)
    obtain ⟨s,t,hst,heq⟩ := W.monochromatic f.vertex
    have hcol := f.edge_eq s t a ((monochromatic_edge_iff W.graph a a s t).mpr ⟨hst,rfl⟩)
    exact T.ne_of_edge hcol heq

/-- `lem:bip`: all actual atom graphs, including unused atoms, are bipartite. -/
theorem atom_bipartite (cco : SemanticCCO T) (a : C) :
    (atomGraph T a).IsBipartite :=
  no_odd_closed_walk_isBipartite _ (no_odd_atom_walk T cco a)

/-- An independent actual bit code, without target homogeneity/transitivity. -/
noncomputable def bitCode (cco : SemanticCCO T) (x : Fin T.size) : Occurring T → Fin 2 :=
  fun a => (atom_bipartite T cco a.val).some x

theorem bitCode_injective (cco : SemanticCCO T) : Function.Injective (bitCode T cco) := by
  intro x y heq
  by_contra hne
  obtain ⟨a,ha⟩ := T.complete x y hne
  let c : Occurring T := ⟨a,x,y,ha⟩
  have hbits := congrFun heq c
  exact ((atom_bipartite T cco a).some.map_rel' ha) hbits

/-- C08: the occurring palette bounds ALL finite symmetric CCO targets,
including the empty and singleton targets and infinitely many unused names. -/
theorem cardinal_le_bits (cco : SemanticCCO T) :
    T.size ≤ 2 ^ Nat.card (Occurring T) := by
  classical
  letI : Fintype (Occurring T) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective _ (bitCode_injective T cco)
  simpa only [Fintype.card_fin,Fintype.card_fun,Nat.card_eq_fintype_card] using h

/-- When all colour names are finite, unused names may simply be retained. -/
theorem cardinal_le_palette [Fintype C] (cco : SemanticCCO T) :
    T.size ≤ 2 ^ Fintype.card C := by
  have h := Nat.card_le_card_of_injective (fun c : Occurring T => c.val) Subtype.val_injective
  exact (cardinal_le_bits T cco).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by simpa only [Nat.card_eq_fintype_card] using h))

end CCO.FiniteFibres
