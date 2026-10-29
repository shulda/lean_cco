import CCO.ProfileHelly.Fill
import Mathlib.Data.Set.Finite.Range
import CCO.ProfileHelly.PathIntersections
import CCO.ProfileHelly.FillPaths
import CCO.ProfileHelly.MissingPairs

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

/-- C18: adding one common old-path colour preserves the DIRECT algebraic
simple-cycle invariant, on the same vertices and with all old edges retained. -/
theorem fill_algebraic (laws : TableLaws T) (alg : D.Algebraic)
    (x y : V) (hxy : x ≠ y) (a : T.Atom (sort x) (sort y))
    (choice : ∀ p : D.graph.Path x y, a ∈ D.pathProfile hxy p) :
    (D.fill x y hxy a).Algebraic := by
  classical
  let E := D.fill x y hxy a
  intro r s hrs p q hd hpq
  have hc := E.disjoint_paths_cycle p q hd hpq
  have hdEdges := ((SimpleGraph.Walk.isTrail_append _ _).mp hc.isTrail).2.2
  by_cases hpnew : s(x,y) ∈ p.val.edges
  · have hqold : s(x,y) ∉ q.val.edges := by
      intro he
      exact hdEdges hpnew (by simpa only [SimpleGraph.Walk.edges_reverse,List.mem_reverse] using he)
    exact D.fill_cycle_new_arc laws x y hxy a choice hrs p.val q.val p.property q.property hc hpnew hqold
  · by_cases hqnew : s(x,y) ∈ q.val.edges
    · have hc' := E.disjoint_paths_cycle q p hd.symm hpq.symm
      have hi := D.fill_cycle_new_arc laws x y hxy a choice hrs q.val p.val
        q.property p.property hc' hqnew hpnew
      obtain ⟨c,hcq,hcp⟩ := hi
      exact ⟨c,hcp,hcq⟩
    · let pp : D.graph.Path r s := ⟨D.transferWalk E p.val
          (D.fill_records_of_avoid x y hxy a p.val hpnew),
        D.transferWalk_isPath E p.val _ p.property⟩
      let qq : D.graph.Path r s := ⟨D.transferWalk E q.val
          (D.fill_records_of_avoid x y hxy a q.val hqnew),
        D.transferWalk_isPath E q.val _ q.property⟩
      have heP : D.pathProfile hrs pp = E.pathProfile hrs p :=
        D.transferWalk_profile E p.val _ (SimpleGraph.Walk.not_nil_of_ne hrs)
      have heQ : D.pathProfile hrs qq = E.pathProfile hrs q :=
        D.transferWalk_profile E q.val _ (SimpleGraph.Walk.not_nil_of_ne hrs)
      rw [← heP,← heQ]
      exact D.path_profiles_intersect laws alg r s hrs pp qq

/-- C20: at termination a specified triangle's closing-edge/profile test
is exactly legality in the original table. This supplies the FULL class. -/
theorem algebraic_triangles (laws : TableLaws T) (alg : D.Algebraic)
    (x y z : V) (hxy : x ≠ y) (_hyz : y ≠ z) (hxz : x ≠ z)
    (a : T.Atom (sort x) (sort y)) (b : T.Atom (sort y) (sort z))
    (c : T.Atom (sort x) (sort z)) (ha : D.edge x y = some a)
    (hb : D.edge y z = some b) (hc : D.edge x z = some c) : T.triangle a b c := by
  classical
  let hab : D.graph.Adj x y := ⟨a,ha⟩
  let hbc : D.graph.Adj y z := ⟨b,hb⟩
  let hac : D.graph.Adj x z := ⟨c,hc⟩
  let p : D.graph.Path x z := ⟨hac.toWalk,hac.isPath_toWalk⟩
  let q : D.graph.Path x z := ⟨SimpleGraph.Walk.cons hab hbc.toWalk,
    (SimpleGraph.Walk.cons_isPath_iff hab hbc.toWalk).mpr
      ⟨hbc.isPath_toWalk,by simpa only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or] using And.intro hxy hxz⟩⟩
  have hp : D.pathProfile hxz p = {c} := by
    change {D.label hac} = {c}
    rw [D.label_unique hac c hc]
  have hq : D.pathProfile hxz q = T.product {a} {b} := by
    change T.product {D.label hab} {D.label hbc} = T.product {a} {b}
    rw [D.label_unique hab a ha,D.label_unique hbc b hb]
  obtain ⟨d,hd,hprod⟩ := D.path_profiles_intersect laws alg x z hxz p q
  rw [hp] at hd
  rw [hq] at hprod
  have he : d = c := hd
  exact (T.product_singleton a b c).mp (he ▸ hprod)

/-- C19--C21: actual finite missing-UNORDERED-pair recursion produces a
FULL complete allowed network on EXACTLY the original vertices and sorts. -/
theorem complete_of_algebraic [Finite V] (laws : TableLaws T)
    (helly : Word.Helly (T := T)) (alg : D.Algebraic) :
    ∃ E : CompleteNetwork T sort, D.Extends E.toNetwork := by
  classical
  have main : ∀ n, ∀ D : Network T sort, D.missingPairs.card = n → D.Algebraic →
      ∃ E : CompleteNetwork T sort, D.Extends E.toNetwork := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro D hn alg
      by_cases hempty : D.missingPairs = ∅
      · let E : CompleteNetwork T sort := {
          toNetwork := D
          complete := D.missingPairs_empty_iff.mp hempty
          legal := D.algebraic_triangles laws alg }
        exact ⟨E,fun _ _ _ he => he⟩
      · obtain ⟨pair,hpair⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hm := (D.mem_missingPairs pair).mp hpair
        induction pair using Sym2.inductionOn with
        | hf x y =>
          obtain ⟨hxy,hmissing⟩ := hm
          obtain ⟨a,hchoice⟩ := D.common_path_colour laws helly alg x y hxy
          have hless : (D.fill x y hxy a).missingPairs.card < n :=
            hn ▸ D.missingPairs_fill_lt x y hxy a hmissing
          obtain ⟨E,hE⟩ := ih _ hless (D.fill x y hxy a) rfl
            (D.fill_algebraic laws alg x y hxy a hchoice)
          exact ⟨E,fun r s b hb => hE r s b (D.fill_extends x y hxy a hmissing r s b hb)⟩
  exact main _ D rfl alg

end CCO.ProfileHelly.Network
