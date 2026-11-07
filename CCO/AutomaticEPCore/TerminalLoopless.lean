import CCO.ParityHasse.Original.ParitySeed
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! B063 C01–C08: an actual terminal homogeneous sort has no nonempty
invariant bipartite graph. The even/connectivity equivalences are FULL
colour-invariant equivalences; no exactness, SAP or CCO assumption enters.
This applies in particular to restrictions of original atoms to a final
sort, even before choosing a current atomic name for that restriction. -/

namespace CCO.AutomaticEPCore

open CCO.ParityHasse.Original

universe u v w r z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Terminality is over EVERY strict cover of the FULL invariant lattice,
including covers with Top upper endpoint. Finite sorts are not excluded. -/
def FullCoverTerminal (i : ι) : Prop :=
  ∀ E F : ColourEq S i, E ⋖ F →
    ∀ x : X i, Infinite (RelativeClass E.val F.val x)

/-- C01: the literal FULL-cover hypothesis excludes every proper finite
relative interval, not just intervals in an exact sublattice. -/
theorem terminal_full_interval_infinite
    (terminal : FullCoverTerminal S i) (E F : ColourEq S i)
    (hEF : E < F) (x : X i) : Infinite (RelativeClass E.val F.val x) := by
  obtain ⟨K,hEK,hKF⟩ := hEF.exists_covby_le
  let : Infinite (RelativeClass E.val K.val x) := terminal E K hEK x
  exact Infinite.of_injective (relativeInclusion E.val K.val F.val hKF x)
    (relativeInclusion_injective E.val K.val F.val hKF x)

/-- Actual finite-length RAW powers are precisely walks of that length.
This is a graph statement; no atomicity or CCO assumption is needed. -/
theorem graph_relPow_iff_walk {A : Type z} (graph : SimpleGraph A)
    (n : Nat) (x y : A) :
    relPow graph.Adj n x y ↔ ∃ p : graph.Walk x y, p.length = n := by
  induction n generalizing x y with
  | zero =>
    constructor
    · intro hxy
      subst y
      exact ⟨.nil,rfl⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => rfl
      | cons h p => simp at hp
  | succ n ih =>
    constructor
    · rintro ⟨a,hxa,hay⟩
      obtain ⟨p,hp⟩ := (ih a y).mp hay
      exact ⟨.cons hxa p,by simp only [SimpleGraph.Walk.length_cons,hp]⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => simp at hp
      | cons h p =>
        refine ⟨_,h,(ih _ _).mpr ⟨p,?_⟩⟩
        simpa only [SimpleGraph.Walk.length_cons,Nat.succ_inj] using hp

/-- A genuine bipartition excludes every odd closed RAW walk. -/
theorem bipartite_graph_no_odd_power {A : Type z} (graph : SimpleGraph A)
    (bipartite : graph.IsBipartite) :
    ∀ x n, Odd n → ¬relPow graph.Adj n x x := by
  classical
  let colour : graph.Coloring Bool :=
    SimpleGraph.recolorOfEquiv graph finTwoEquiv bipartite.some
  intro x n hn hpow
  obtain ⟨p,hp⟩ := (graph_relPow_iff_walk graph n x x).mp hpow
  have he : Even p.length := (colour.even_length_iff_congr p).mpr Iff.rfl
  have ho : Odd p.length := hp ▸ hn
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- C02: a nonempty actual invariant graph is serial on the SAME sort. -/
theorem invariant_graph_serial (H : HomogeneousSource S G)
    (graph : SimpleGraph (X i)) (invariant : ColourInvariant S i graph.Adj)
    (nonempty : ∃ x y, graph.Adj x y) : ∀ x, ∃ y, graph.Adj x y :=
  invariant_nonempty_serial S H invariant nonempty

/-- C03: the actual even-walk equivalence, with length zero included. -/
def invariantGraphEvenEq (H : HomogeneousSource S G)
    (graph : SimpleGraph (X i)) (invariant : ColourInvariant S i graph.Adj) :
    ColourEq S i :=
  ⟨evenSetoid graph.Adj (fun _ _ h => graph.adj_symm h),by
    intro x y x' y' hcol
    constructor
    · rintro ⟨n,hn,hxy⟩
      exact ⟨n,hn,(colourInvariant_relPow S H invariant n _ _ _ _ hcol).mp hxy⟩
    · rintro ⟨n,hn,hxy⟩
      exact ⟨n,hn,(colourInvariant_relPow S H invariant n _ _ _ _ hcol).mpr hxy⟩⟩

/-- C03: the actual all-walk connectivity equivalence, with no exactness
claim. Both endpoints live in the FULL actual invariant lattice. -/
def invariantGraphConnectivityEq (H : HomogeneousSource S G)
    (graph : SimpleGraph (X i)) (invariant : ColourInvariant S i graph.Adj) :
    ColourEq S i :=
  ⟨connectivitySetoid graph.Adj (fun _ _ h => graph.adj_symm h),by
    intro x y x' y' hcol
    constructor
    · rintro ⟨n,hxy⟩
      exact ⟨n,(colourInvariant_relPow S H invariant n _ _ _ _ hcol).mp hxy⟩
    · rintro ⟨n,hxy⟩
      exact ⟨n,(colourInvariant_relPow S H invariant n _ _ _ _ hcol).mpr hxy⟩⟩

/-- C03: finite actual orbitals give positive stabilized parity relations.
The relation need not itself have been named as one current atom. -/
theorem invariant_graph_positive_parity_stabilization
    (H : HomogeneousSource S G) (graph : SimpleGraph (X i))
    (invariant : ColourInvariant S i graph.Adj)
    (nonempty : ∃ x y, graph.Adj x y) :
    ∃ N : Nat, 0 < N ∧
      (∀ x y, invariantGraphEvenEq S H graph invariant x y ↔
        relPow graph.Adj (2*N) x y) ∧
      (∀ x y, OddWalk graph.Adj x y ↔ relPow graph.Adj (2*N+1) x y) := by
  obtain ⟨N,hN,he,ho,_,_⟩ := exists_positive_parity_stabilization S H invariant
    (fun _ _ h => graph.adj_symm h) (invariant_graph_serial S H graph invariant nonempty)
  refine ⟨N,hN,?_,?_⟩
  · intro x y
    constructor
    · rintro ⟨n,hn,hxy⟩
      obtain ⟨k,rfl⟩ := even_iff_exists_two_mul.mp hn
      exact he k x y hxy
    · intro hxy
      exact ⟨2*N,even_two.mul_right N,hxy⟩
  · intro x y
    constructor
    · rintro ⟨n,hn,hxy⟩
      obtain ⟨k,rfl⟩ := odd_iff_exists_bit1.mp hn
      exact ho k x y hxy
    · intro hxy
      exact ⟨2*N+1,(even_two.mul_right N).add_one,hxy⟩

/-- C04: the two genuine parity classes in every connected component of
one nonempty invariant bipartite graph have exact relative index TWO. -/
theorem invariant_bipartite_parity_index_two
    (H : HomogeneousSource S G) (graph : SimpleGraph (X i))
    (invariant : ColourInvariant S i graph.Adj)
    (nonempty : ∃ x y, graph.Adj x y) (bipartite : graph.IsBipartite)
    (a : X i) :
    relativeIndex (invariantGraphEvenEq S H graph invariant).val
      (invariantGraphConnectivityEq S H graph invariant).val a = 2 := by
  obtain ⟨b,hab⟩ := invariant_graph_serial S H graph invariant nonempty a
  let E := invariantGraphEvenEq S H graph invariant
  let F := invariantGraphConnectivityEq S H graph invariant
  have noOdd := bipartite_graph_no_odd_power graph bipartite
  have hob : OddWalk graph.Adj a b := ⟨1,odd_one,(relPow_one _ _ _).mpr hab⟩
  have hFab : F a b := ⟨1,(relPow_one _ _ _).mpr hab⟩
  let qa : RelativeClass E.val F.val a := Quotient.mk _ ⟨a,F.val.refl a⟩
  let qb : RelativeClass E.val F.val a := Quotient.mk _ ⟨b,hFab⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qa,qb,?_,?_⟩
  · intro h
    have hE := Quotient.exact h
    exact even_odd_disjoint graph.Adj (fun _ _ h => graph.adj_symm h) noOdd a b ⟨hE,hob⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rcases (connectedWalk_iff_even_or_odd graph.Adj a x.val).mp x.property with he | ho
    · exact Or.inl (Quotient.sound (E.val.symm he))
    · apply Or.inr
      apply Quotient.sound
      rcases ho with ⟨n,hn,hax⟩
      refine ⟨n+1,hn.add_one,?_⟩
      rw [relPow_add]
      exact ⟨a,relPow_symmetric graph.Adj (fun _ _ h => graph.adj_symm h) n a x.val hax,
        (relPow_one _ _ _).mpr hab⟩

/-- C04: the parity interval is an actual strict FULL invariant cover. -/
theorem invariant_bipartite_parity_cover
    (H : HomogeneousSource S G) (graph : SimpleGraph (X i))
    (invariant : ColourInvariant S i graph.Adj)
    (nonempty : ∃ x y, graph.Adj x y) (bipartite : graph.IsBipartite) :
    invariantGraphEvenEq S H graph invariant ⋖
      invariantGraphConnectivityEq S H graph invariant := by
  obtain ⟨a⟩ := S.nonemptySort i
  exact covBy_of_relativeIndex_two S H _ _
    (fun _ _ ⟨n,_,hn⟩ => ⟨n,hn⟩) a
    (invariant_bipartite_parity_index_two S H graph invariant nonempty bipartite a)

/-- C05–C08: a genuine terminal homogeneous sort has no nonempty
colour-invariant bipartite graph. Only FULL terminality is used. -/
theorem terminal_invariant_bipartite_graph_empty
    (H : HomogeneousSource S G) (terminal : FullCoverTerminal S i)
    (graph : SimpleGraph (X i)) (invariant : ColourInvariant S i graph.Adj)
    (bipartite : graph.IsBipartite) : ∀ x y, ¬graph.Adj x y := by
  intro x y hxy
  let E := invariantGraphEvenEq S H graph invariant
  let F := invariantGraphConnectivityEq S H graph invariant
  have nonempty : ∃ x y, graph.Adj x y := ⟨x,y,hxy⟩
  have hcover := invariant_bipartite_parity_cover S H graph invariant nonempty bipartite
  let : Infinite (RelativeClass E.val F.val x) := terminal E F hcover x
  have hzero : relativeIndex E.val F.val x = 0 := Nat.card_eq_zero_of_infinite
  have htwo := invariant_bipartite_parity_index_two S H graph invariant nonempty bipartite x
  exact (by decide : (0 : Nat) ≠ 2) (hzero.symm.trans htwo)

/-- C05/C06 receiving form for an ORIGINAL bipartite graph pulled back
to one actual current homogeneous sort. The caller supplies only the
proved current-colour invariance of that literal restriction. -/
theorem terminal_bipartite_restriction_empty
    (H : HomogeneousSource S G) (terminal : FullCoverTerminal S i)
    {A : Type z} (oldGraph : SimpleGraph A) (realPoint : X i → A)
    (invariant : ColourInvariant S i (fun x y => oldGraph.Adj (realPoint x) (realPoint y)))
    (bipartite : oldGraph.IsBipartite) :
    ∀ x y, ¬oldGraph.Adj (realPoint x) (realPoint y) := by
  exact terminal_invariant_bipartite_graph_empty S H terminal
    (oldGraph.comap realPoint) invariant
    (SimpleGraph.Colorable.of_hom (SimpleGraph.Hom.comap realPoint oldGraph) bipartite)

/-- In a terminal source every occurring same-sort diversity atom is
nonbipartite. This includes finite and zero-step source cases literally. -/
theorem terminal_atom_not_bipartite
    (H : HomogeneousSource S G) (terminal : FullCoverTerminal S i)
    (c : S.Atom i i) : ¬(atomGraph S c).IsBipartite := by
  intro bipartite
  have invariant : ColourInvariant S i (atomGraph S c).Adj := by
    intro x y x' y' hcol
    change S.colour x y = some c ↔ S.colour x' y' = some c
    rw [hcol]
  obtain ⟨x,y,hxy⟩ := S.realized c
  exact terminal_invariant_bipartite_graph_empty S H terminal
    (atomGraph S c) invariant bipartite x y hxy

/-- C07: support of genuine real equality is literal type equality,
using realization of every type. It is not a diversity support loop. -/
theorem equality_support_iff {A : Type z} {T : Type*}
    (label : A → T) (realized : Function.Surjective label) (s t : T) :
    (∃ x y : A, label x = s ∧ label y = t ∧ x = y) ↔ s = t := by
  constructor
  · rintro ⟨x,y,hx,hy,rfl⟩
    exact hx.symm.trans hy
  · intro hst
    obtain ⟨x,hx⟩ := realized s
    exact ⟨x,x,hx,hx.trans hst,rfl⟩

/-- C07: a diagonal diversity-graph support is witnessed by TWO DISTINCT
real points of the same type; it never asserts a real equality edge. -/
theorem diversity_support_diagonal_iff {A : Type z} {T : Type*}
    (graph : SimpleGraph A) (label : A → T) (t : T) :
    (∃ x y, label x = t ∧ label y = t ∧ graph.Adj x y) ↔
      ∃ x y, x ≠ y ∧ label x = t ∧ label y = t ∧ graph.Adj x y := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    exact ⟨x,y,graph.ne_of_adj hxy,hx,hy,hxy⟩
  · rintro ⟨x,y,_,hx,hy,hxy⟩
    exact ⟨x,y,hx,hy,hxy⟩

end CCO.AutomaticEPCore
