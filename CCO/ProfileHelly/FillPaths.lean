import CCO.ProfileHelly.EdgeCycles

universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)
open SimpleGraph

theorem fill_records_of_avoid (x y : V) (hxy : x ≠ y) (a : T.Atom (sort x) (sort y))
    {p q : V} (w : (D.fill x y hxy a).graph.Walk p q) (hn : s(x,y) ∉ w.edges) :
    ∀ {r s}, s(r,s) ∈ w.edges → (D.fill x y hxy a).edge r s = D.edge r s := by
  intro r s hrs
  apply D.fill_other x y hxy a r s
  · rintro ⟨rfl,rfl⟩
    exact hn hrs
  · rintro ⟨rfl,rfl⟩
    exact hn (by simpa only [Sym2.eq_swap] using hrs)

/-- The common old path colour is valid in BOTH orientations of the new
unordered edge, with the literal typed converse. -/
theorem fill_edge_choice (laws : TableLaws T) (x y : V) (hxy : x ≠ y)
    (a : T.Atom (sort x) (sort y))
    (choice : ∀ p : D.graph.Path x y, a ∈ D.pathProfile hxy p)
    {r s : V} (hrs : r ≠ s) (hpair : s(r,s) = s(x,y))
    (b : T.Atom (sort r) (sort s)) (hb : (D.fill x y hxy a).edge r s = some b)
    (p : D.graph.Path r s) : b ∈ D.pathProfile hrs p := by
  rcases Sym2.eq_iff.mp hpair with ⟨hr,hs⟩ | ⟨hr,hs⟩
  · subst r
    subst s
    have he : a = b := Option.some.inj ((D.fill_forward x y hxy a).symm.trans hb)
    exact he ▸ choice p
  · subst r
    subst s
    have he : T.conv a = b := Option.some.inj ((D.fill_backward x y hxy a).symm.trans hb)
    subst b
    let q : D.graph.Path x y := ⟨p.val.reverse,p.property.reverse⟩
    have hc := choice q
    change a ∈ D.walkProfile p.val.reverse (D.reverse_not_nil p.val (Walk.not_nil_of_ne hrs)) at hc
    rw [D.walkProfile_reverse laws] at hc
    exact hc

/-- A new cycle is read at its genuinely new edge. OLD leading edges are
moved across the arc by set Peirce until that edge is first; the OLD simple
complement supplies the chosen colour. No semantic completion is used. -/
theorem fill_cycle_new_arc (laws : TableLaws T) (x y : V) (hxy : x ≠ y)
    (a : T.Atom (sort x) (sort y))
    (choice : ∀ p : D.graph.Path x y, a ∈ D.pathProfile hxy p)
    {r s : V} (hrs : r ≠ s) (p q : (D.fill x y hxy a).graph.Walk r s)
    (hp : p.IsPath) (hq : q.IsPath) (hc : (p.append q.reverse).IsCycle)
    (hnew : s(x,y) ∈ p.edges) (hold : s(x,y) ∉ q.edges) :
    ((D.fill x y hxy a).walkProfile p (Walk.not_nil_of_ne hrs) ∩
      (D.fill x y hxy a).walkProfile q (Walk.not_nil_of_ne hrs)).Nonempty := by
  classical
  let E := D.fill x y hxy a
  have main : ∀ n, ∀ (r s : V) (hrs : r ≠ s) (p q : E.graph.Walk r s), p.length = n →
      p.IsPath → q.IsPath → (p.append q.reverse).IsCycle →
      s(x,y) ∈ p.edges → s(x,y) ∉ q.edges →
      (E.walkProfile p (Walk.not_nil_of_ne hrs) ∩ E.walkProfile q (Walk.not_nil_of_ne hrs)).Nonempty := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro r s hrs p q hn hp hq hc hnew hold
      cases p with
      | nil => cases hnew
      | @cons r t s h tail =>
        by_cases hhead : s(r,t) = s(x,y)
        · have htail_old : s(x,y) ∉ tail.edges := by
            have hh := hp.isTrail.edges_nodup
            rw [Walk.edges_cons,List.nodup_cons] at hh
            simpa only [hhead] using hh.1
          cases tail with
          | nil =>
            let qr := D.transferWalk E q (D.fill_records_of_avoid x y hxy a q hold)
            let qD : D.graph.Path r s := ⟨qr,D.transferWalk_isPath E q _ hq⟩
            have hb := D.fill_edge_choice laws x y hxy a choice hrs hhead
              (E.label h) (E.label_spec h) qD
            have he := D.transferWalk_profile E q (D.fill_records_of_avoid x y hxy a q hold)
              (Walk.not_nil_of_ne hrs)
            have hb' : E.label h ∈ E.walkProfile q (Walk.not_nil_of_ne hrs) := he ▸ hb
            exact ⟨E.label h,rfl,hb'⟩
          | cons k tail =>
            let w := q.append (Walk.cons k tail).reverse
            have hw : w.IsPath := E.cycle_head_complement h (Walk.cons k tail) q hc
            have hwo : s(x,y) ∉ w.edges := by
              simpa only [w,Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse,not_or]
                using And.intro hold htail_old
            let wr := D.transferWalk E w (D.fill_records_of_avoid x y hxy a w hwo)
            let wD : D.graph.Path r t := ⟨wr,D.transferWalk_isPath E w _ hw⟩
            have hb := D.fill_edge_choice laws x y hxy a choice h.ne hhead
              (E.label h) (E.label_spec h) wD
            have he := D.transferWalk_profile E w (D.fill_records_of_avoid x y hxy a w hwo)
              (Walk.not_nil_of_ne h.ne)
            have hb' : E.label h ∈ E.walkProfile w (Walk.not_nil_of_ne h.ne) := he ▸ hb
            have heq := E.walkProfile_append laws q (Walk.cons k tail).reverse
              (Walk.not_nil_of_ne hrs) (E.reverse_not_nil _ Walk.not_nil_cons)
            have hbc : E.label h ∈ T.product (E.walkProfile q (Walk.not_nil_of_ne hrs))
                (T.opposite (E.walkProfile (Walk.cons k tail) Walk.not_nil_cons)) := by
              rw [E.walkProfile_reverse laws] at heq
              exact heq ▸ hb'
            change (T.product {E.label h} (E.walkProfile (Walk.cons k tail) Walk.not_nil_cons) ∩
              E.walkProfile q (Walk.not_nil_of_ne hrs)).Nonempty
            exact (T.set_peirce_left _ _ _).mpr ⟨E.label h,rfl,hbc⟩
        · have htnew : s(x,y) ∈ tail.edges :=
            (List.mem_cons.mp hnew).resolve_left (fun he => hhead he.symm)
          have htn : ¬tail.Nil := by
            intro he
            cases he
            cases htnew
          have hts : t ≠ s := fun he => htn ((hp.of_cons.nil_iff_eq).mpr he)
          let q' := Walk.cons h.symm q
          have hc' : (tail.append q'.reverse).IsCycle := E.cycle_move_head h tail q hc
          have hq' : q'.IsPath := (Walk.isPath_reverse_iff q').mp (hc'.isPath_of_append_right htn)
          have ho' : s(x,y) ∉ q'.edges := by
            intro he
            rcases List.mem_cons.mp he with he | he
            · exact hhead ((show s(r,t) = s(t,r) from Sym2.eq_swap).trans he.symm)
            · exact hold he
          have hlen : tail.length < n := by
            change tail.length + 1 = n at hn
            omega
          have hi := ih tail.length hlen t s hts tail q' rfl hp.of_cons hq' hc' htnew ho'
          exact (E.move_head_intersection h tail q htn (Walk.not_nil_of_ne hrs)).mpr hi
  exact main p.length r s hrs p q rfl hp hq hc hnew hold

end CCO.ProfileHelly.Network
