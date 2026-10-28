import CCO.ParityHasse.Original.ParitySeed

/-! B011 C25–26: terminal ORIGINAL full invariant lattices. All words remain
on a fixed named original sort of the ambient source. The acting group is
the same ambient G throughout. No CCO, SAP or distributivity is assumed. -/
universe u v w t
namespace CCO.RealClosure.Bounds
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- No relative-index-two interval in the FULL original invariant lattice
on the displayed original sort. Endpoints need not be exact. -/
def SortNR2 : Prop :=
  ∀ E F : ColourEq S i, E ≤ F → ∀ a : X i, relativeIndex E.val F.val a ≠ 2

variable {i}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

private theorem atomic_colour (c : S.Atom i i) : ColourInvariant S i (S.atomRel c) := by
  intro x y x' y' hc
  change S.colour x y = some c ↔ S.colour x' y' = some c
  rw [hc]

private theorem atomic_symmetric (c : S.Atom i i) :
    ∀ x y, S.atomRel c x y → S.atomRel c y x :=
  colourInvariant_symmetric S (atomic_colour S H c)

private theorem atomic_serial (c : S.Atom i i) : ∀ x, ∃ y, S.atomRel c x y :=
  invariant_nonempty_serial S H (atomic_colour S H c) (S.realized c)

/-- Absence of odd closed walks would exhibit the actual original full
index-two interval of the accepted parity seed, contradicting the premise. -/
theorem terminal_exists_odd_closed (nr2 : SortNR2 S i) (c : S.Atom i i) :
    ∃ x n, Odd n ∧ relPow (S.atomRel c) n x x := by
  by_contra hn
  have noOdd : ∀ x n, Odd n → ¬ relPow (S.atomRel c) n x x := by
    intro x n ho hw
    exact hn ⟨x,n,ho,hw⟩
  obtain ⟨a⟩ := S.nonemptySort i
  exact nr2 (evenColourEq S H c) (connectivityColourEq S H c)
    (even_le_connectivity S H c) a (parity_seed_index_two S H c noOdd a)

/-- Ambient original transitivity moves an odd closed walk to EVERY real
point. Thus every actual atomic component, not merely one, is nonbipartite. -/
theorem terminal_every_point_odd (nr2 : SortNR2 S i) (c : S.Atom i i) (x : X i) :
    ∃ n, Odd n ∧ relPow (S.atomRel c) n x x := by
  obtain ⟨y,n,ho,hw⟩ := terminal_exists_odd_closed S H nr2 c
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i y x
  have hc : ColourInvariant S i (relPow (S.atomRel c) n) :=
    colourInvariant_relPow S H (atomic_colour S H c) n
  have hh := colourInvariant_groupInvariant S H hc g y y hw
  exact ⟨n,ho,by simpa only [hg] using hh⟩

/-- Literal odd closed GRAPH walks witness nonbipartiteness in each component. -/
theorem terminal_component_odd_walk (nr2 : SortNR2 S i) (c : S.Atom i i) (x : X i) :
    ∃ p : (atomGraph S c).Walk x x, Odd p.length := by
  obtain ⟨n,ho,hw⟩ := terminal_every_point_odd S H nr2 c x
  obtain ⟨p,hp⟩ := (relPow_atom_iff_walk S c n x x).mp hw
  exact ⟨p,hp.symm ▸ ho⟩

/-- The odd detour changes parity of any same-component walk, with actual
equality endpoints retained. Neither an exactness nor a Helly premise occurs. -/
theorem terminal_even_iff_connected (nr2 : SortNR2 S i) (c : S.Atom i i)
    (x y : X i) : evenColourEq S H c x y ↔ connectivityColourEq S H c x y := by
  constructor
  · intro h
    exact even_le_connectivity S H c h
  · intro hxy
    rcases (connectivity_eq_even_union_odd S H c x y).mp hxy with he | ho
    · exact he
    · obtain ⟨n,hn,hxx⟩ := terminal_every_point_odd S H nr2 c x
      obtain ⟨m,hm,hxy⟩ := ho
      refine ⟨n+m,hn.add_odd hm,?_⟩
      rw [relPow_add]
      exact ⟨x,hxx,hxy⟩

theorem terminal_odd_iff_connected (nr2 : SortNR2 S i) (c : S.Atom i i)
    (x y : X i) : OddWalk (S.atomRel c) x y ↔ connectivityColourEq S H c x y := by
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩
  · intro hxy
    obtain ⟨m,hm,hxy⟩ := (terminal_even_iff_connected S H nr2 c x y).mpr hxy
    obtain ⟨n,hn,hxx⟩ := terminal_every_point_odd S H nr2 c x
    refine ⟨n+m,hn.add_even hm,?_⟩
    rw [relPow_add]
    exact ⟨x,hxx,hxy⟩

/-- Finite OLD pair orbitals give one uniform threshold for ALL ordered
pairs (including equality) in ALL actual components. Every sufficiently
large literal atomic power is the full original connectivity equivalence. -/
theorem terminal_uniform_atomic_powers (nr2 : SortNR2 S i) (c : S.Atom i i) :
    ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      RawWord.relation S (atomWord S c n) = (connectivityColourEq S H c).val.r := by
  obtain ⟨N,hN,he,ho,hest,host⟩ := exists_positive_parity_stabilization S H
    (atomic_colour S H c) (atomic_symmetric S H c) (atomic_serial S H c)
  refine ⟨2*N,by omega,?_⟩
  intro n hn
  rw [atomWord_relation]
  funext x y
  apply propext
  constructor
  · intro hxy
    exact ⟨n,hxy⟩
  · intro hxy
    rcases Nat.even_or_odd n with hen | hon
    · obtain ⟨k,hk⟩ := even_iff_exists_two_mul.mp hen
      have hNk : N ≤ k := by omega
      obtain ⟨l,hl,hw⟩ := (terminal_even_iff_connected S H nr2 c x y).mpr hxy
      obtain ⟨j,hj⟩ := even_iff_exists_two_mul.mp hl
      subst l
      have hh := he j x y hw
      rw [hest k hNk] at hh
      simpa only [hk] using hh
    · obtain ⟨k,hk⟩ := odd_iff_exists_bit1.mp hon
      have hNk : N ≤ k := by omega
      obtain ⟨l,hl,hw⟩ := (terminal_odd_iff_connected S H nr2 c x y).mpr hxy
      obtain ⟨j,hj⟩ := odd_iff_exists_bit1.mp hl
      subst l
      have hh := ho j x y hw
      rw [host k hNk] at hh
      simpa only [hk] using hh

theorem terminal_connectivity_one_word (nr2 : SortNR2 S i) (c : S.Atom i i) :
    ∃ w : RawWord S i i, RawWord.relation S w = (connectivityColourEq S H c).val.r := by
  obtain ⟨N,_,hN⟩ := terminal_uniform_atomic_powers S H nr2 c
  exact ⟨atomWord S c N,hN N le_rfl⟩

end CCO.RealClosure.Bounds
