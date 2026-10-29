import CCO.TerminalPowers.GraphSource

/-! Short constructive graph consequences of the selected accepted parity
providers: original-action transport, odd detours and literal two-step padding.
No uniform-threshold provider is duplicated here. -/
universe u v w t
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)] (H : HomogeneousSource S G)
variable {i : ι}

include H in
theorem represented_walk_transport (t : S.Atom i i) (g : G) (n : Nat) (x y : X i)
    (h : relPow (S.atomRel t) n x y) : relPow (S.atomRel t) n (g • x) (g • y) := by
  apply colourInvariant_groupInvariant S H
    (colourInvariant_relPow S H (fun a b a' b' hc => by
      change S.colour a b = some t ↔ S.colour a' b' = some t
      rw [hc]) n) g x y h

include H in
/-- C02/C04: original whole-source motions transport components and odd
closed walks, so a parity obstruction at one point holds at every point. -/
theorem odd_closed_transport (t : S.Atom i i) (x y : X i) :
    (∃ n, Odd n ∧ relPow (S.atomRel t) n x x) ↔
      ∃ n, Odd n ∧ relPow (S.atomRel t) n y y := by
  constructor
  · rintro ⟨n,hn,hw⟩
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
    exact ⟨n,hn,by simpa only [hg] using represented_walk_transport S H t g n x x hw⟩
  · rintro ⟨n,hn,hw⟩
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i y x
    exact ⟨n,hn,by simpa only [hg] using represented_walk_transport S H t g n y y hw⟩

include H in
theorem nr2_odd_closed_ge_three (nr2 : SortNR2 S i) (t : S.Atom i i) (x : X i) :
    ∃ p : (atomGraph S t).Walk x x, Odd p.length ∧ 3 ≤ p.length := by
  obtain ⟨p,hp⟩ := nr2_odd_walk S H nr2 t x
  have hne : p.length ≠ 1 := by
    intro he
    exact (SimpleGraph.Walk.adj_of_length_eq_one he).ne rfl
  have ho := Nat.odd_iff.mp hp
  exact ⟨p,hp,by omega⟩

include H in
/-- C08: the accepted two-step backtrack stays at the same literal endpoints. -/
theorem prepend_backtracks (t : S.Atom i i) {x y : X i} {n : Nat}
    (h : relPow (S.atomRel t) n x y) (k : Nat) :
    relPow (S.atomRel t) (n+2*k) x y := by
  induction k with
  | zero => simpa only [Nat.mul_zero,Nat.add_zero] using h
  | succ k ih =>
    have hn := relPow_mono_two (S.atomRel t)
      (fun x y h => by simpa only [AtomicSource.atomRel,S.symmetricLoop] using (S.colour_swap x y t).mp h)
      (fun x => by obtain ⟨y,_,hy⟩ := atom_neighbour S H t x; exact ⟨y,hy⟩)
      (n+2*k) x y ih
    convert hn using 1

/-- C09: a connected distinct pair has positive opposite-parity base walks. -/
theorem opposite_parity_walks (nr2 : SortNR2 S i) (t : S.Atom i i)
    {x y : X i} (hne : x ≠ y) (hxy : Connected S H t x y) :
    ∃ l m : Nat, 0 < l ∧ 3 ≤ m ∧ Odd m ∧ relPow (S.atomRel t) l x y ∧
      relPow (S.atomRel t) (m+l) x y := by
  obtain ⟨l,hl⟩ := hxy
  obtain ⟨p,hp,hthree⟩ := nr2_odd_closed_ge_three S H nr2 t x
  have hloop := (relPow_atom_iff_walk S t p.length x x).mpr ⟨p,rfl⟩
  have hlpos : 0 < l := by
    by_contra hn
    have he : l = 0 := by omega
    rw [he] at hl
    exact hne hl
  refine ⟨l,p.length,hlpos,hthree,hp,hl,?_⟩
  rw [relPow_add]
  exact ⟨x,hloop,hl⟩

/-- C10: a finite odd detour and two-edge padding yield EVERY large length,
with the same actual literal endpoints, rather than only a subsequence. -/
theorem pair_all_large_lengths (nr2 : SortNR2 S i) (t : S.Atom i i)
    {x y : X i} (hne : x ≠ y) (hxy : Connected S H t x y) :
    ∃ N : Nat, 0 < N ∧ ∀ n, N ≤ n → relPow (S.atomRel t) n x y := by
  obtain ⟨l,m,hl,hm,hodd,hbase,hdetour⟩ := opposite_parity_walks S H nr2 t hne hxy
  refine ⟨m+l,by omega,?_⟩
  intro n hn
  rcases Nat.even_or_odd (n-l) with he | ho
  · obtain ⟨k,hk⟩ := he
    have heq : n = l+2*k := by omega
    rw [heq]
    exact prepend_backtracks S H t hbase k
  · have he : Even (n-(m+l)) := by
      apply Nat.even_iff.mpr
      have h₁ := Nat.odd_iff.mp hodd
      have h₂ := Nat.odd_iff.mp ho
      omega
    obtain ⟨k,hk⟩ := he
    have heq : n = (m+l)+2*k := by omega
    rw [heq]
    exact prepend_backtracks S H t hdetour k

end CCO.TerminalPowers
