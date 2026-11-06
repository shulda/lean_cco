import CCO.TerminalPowers.Saturation

/-!
# Source11 T02: actual long monochromatic clone cycles

The source pure-power theorem is used at the positive exponent one less
than the cycle length. Its endpoint diversity colour is the very same
old atom as every displayed clone edge. Closing that represented path by
one genuine old edge gives a homomorphism of the original simple cycle.

Only the literal sort and colour readings of the specified cycle are
required. No long-cycle completion provider, semantic CCO invocation,
hidden-source SAP, or new atomic relation is assumed here.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalPowers CCO.RealClosure.Bounds

universe u v w z t

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The actual terminal STRONG power threshold supplies a cyclic
old `e`-walk of EVERY sufficiently large length. In particular the
exponent is positive and no logical diagonal is inserted into the
diversity profile. -/
theorem original_same_sort_pure_power_cycle_threshold
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (nr2 : SortNR2 S i) (e : S.Atom i i) :
    ∃ N : ℕ+, ∀ ℓ : Nat, N.val + 1 ≤ ℓ →
      CyclicWalk (atomGraph S e) ℓ := by
  obtain ⟨N,hN⟩ := terminal_pure_power S H sap nr2 e
  refine ⟨N,?_⟩
  intro ℓ hLarge
  have hPos : 0 < N.val := N.property
  let n : ℕ+ := ⟨ℓ - 1, by omega⟩
  have hBound : N.val ≤ n.val := by
    change N.val ≤ ℓ - 1
    omega
  have hProfile : e ∈ purePower S e n := by
    rw [hN n hBound]
    exact atom_mem_connectivityPalette S H e
  rw [purePower_eq_guarded S H sap e n] at hProfile
  obtain ⟨x,y,hPath,hColour⟩ := hProfile
  obtain ⟨p,hp⟩ := (relPow_atom_iff_walk S e n.val x y).mp hPath
  have hBack : (atomGraph S e).Adj y x :=
    (atomGraph S e).adj_symm hColour
  let q : (atomGraph S e).Walk x x := p.append (.cons hBack .nil)
  have hLength : q.length = ℓ := by
    simp only [q, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hp]
    dsimp [n]
    have := N.property
    omega
  have hCyclic := cyclicWalk_of_closed q (by omega)
  simpa only [hLength] using hCyclic

private theorem original_cycle_colour_transport
    {i j k : ι} (hj : j = i) (hk : k = i)
    (a : S.Atom j k) (e : S.Atom i i) (ha : HEq a e)
    (x y : X i) (hxy : S.colour x y = some e) :
    S.colour (hj.symm ▸ x) (hk.symm ▸ y) = some a := by
  cases hj
  cases hk
  have hEqual : a = e := eq_of_heq ha
  subst a
  exact hxy

/-- Read a genuine monochromatic old cyclic walk onto the SAME original
specified simple cycle, preserving every old dependent sort and atom.
The two premises are literal readings of its displayed edges. -/
theorem original_monochromatic_cycle_hom_of_cyclic_walk
    {V : Type z} {D : PartialDiagram S V}
    (C : SimpleCycle D) {i : ι} (e : S.Atom i i)
    (hSort : ∀ p : Fin C.length, D.vertexSort (C.vertices p) = i)
    (hAtom : ∀ (p : Fin C.length)
      (a : S.Atom (D.vertexSort (C.vertices p))
        (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
      D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
        (C.next_ne p) = some a → HEq a e)
    (hWalk : CyclicWalk (atomGraph S e) C.length) :
    CycleHom C := by
  obtain ⟨_,point,hEdges⟩ := hWalk
  refine ⟨fun p => (hSort p).symm ▸ point p, ?_⟩
  intro p a ha
  apply original_cycle_colour_transport S (hSort p)
    (hSort (cyclicNext C.length_pos p)) a e (hAtom p a ha)
  exact hEdges p

/-- Actual source11 clone-cycle test. The one original positive power
threshold is selected before varying the simple cycle. Its only later
tests are the real length bound and actual monochromatic sort/edge
readings; old homogeneity, SAP and NR2 discharge realizability. -/
theorem original_clone_cycle_hom_of_terminal_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (nr2 : SortNR2 S i) (e : S.Atom i i) :
    ∃ N : ℕ+, ∀ {V : Type z} {D : PartialDiagram S V}
      (C : SimpleCycle D), N.val + 1 ≤ C.length →
      (∀ p : Fin C.length, D.vertexSort (C.vertices p) = i) →
      (∀ (p : Fin C.length)
        (a : S.Atom (D.vertexSort (C.vertices p))
          (D.vertexSort (C.vertices (cyclicNext C.length_pos p)))),
        D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
          (C.next_ne p) = some a → HEq a e) →
      CycleHom C := by
  obtain ⟨N,hN⟩ := original_same_sort_pure_power_cycle_threshold S H sap nr2 e
  refine ⟨N,?_⟩
  intro V D C hLarge hSort hAtom
  exact original_monochromatic_cycle_hom_of_cyclic_walk S C e hSort hAtom
    (hN C.length hLarge)

end CCO.TypedOrbitFrames
