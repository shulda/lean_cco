import CCO.FullCode.Roots

/-! Exact marked presentation support, including all partial domains. -/
universe u v w a b
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}

theorem Term.path_represented {C : Structure L V} {x y : V} {s : L.Sorts}
    (hs : C.sort x = s) (h : Relation.ReflTransGen C.Step x y) :
    ∃ t, ∃ q : Term L s t, y ∈ q.eval C x := by
  induction h with
  | refl => exact ⟨s, .id s, rfl⟩
  | @tail y z h hstep ih =>
    obtain ⟨t, q, hq⟩ := ih
    obtain ⟨F, hF⟩ := hstep
    have ht : t = L.input F := (q.sorted C hs hq).symm.trans (C.func_sorted F y z hF).1
    subst t
    exact ⟨L.output F, .app F q, y, hq, hF⟩

theorem Term.eval_mem_closure {C : Structure L V} {s t : L.Sorts}
    (q : Term L s t) {T : Set V} {x y : V} (hx : x ∈ C.closure T)
    (hy : y ∈ q.eval C x) : y ∈ C.closure T := by
  induction q generalizing y with
  | id => exact (Set.mem_singleton_iff.mp hy) ▸ hx
  | app F q ih =>
    obtain ⟨z, hz, hy⟩ := hy
    exact C.isClosed_closure T F z (ih hz) hy

theorem Root.coordinateGraph_sorted {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (q : Coordinate S) {x : V} (hx : x ∈ r.coordinateGraph q) :
    C.sort x = S.coordinateSort q.1 q.2 := by
  cases q with | mk qt qj =>
   obtain ⟨h, rfl⟩ := hx
   cases h
   exact r.sorted qj

theorem Root.presentation_sorted {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (N : NormalForms L) (p : Presentation N S) {x : V}
    (hx : x ∈ r.presentation N p) : C.sort x = p.2.1 := by
  obtain ⟨z, hz, hx⟩ := hx
  exact (N.form _ _ p.2.2).sorted C (r.coordinateGraph_sorted _ hz) hx

namespace Object
variable {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type a} {B : Type b}

theorem presentation_mem_support (O : Object C S A) (N : NormalForms L)
    (a : A) (p : Presentation N S) {x : V} (hx : x ∈ (O.root a).presentation N p) :
    x ∈ O.support := by
  obtain ⟨z, ⟨h, rfl⟩, hx⟩ := hx
  exact (N.form _ _ p.2.2).eval_mem_closure (O.coordinate_mem_support a _) hx

theorem mem_support_iff_presentation (O : Object C S A) (N : NormalForms L)
    (hN : N.Valid C) (x : V) :
    x ∈ O.support ↔ ∃ a p, x ∈ (O.root a).presentation N p := by
  constructor
  · rintro ⟨z, ⟨a, j, rfl⟩, hpath⟩
    obtain ⟨t, q, hq⟩ := Term.path_represented ((O.root a).sorted j) hpath
    refine ⟨a, ⟨⟨(O.root a).tag, j⟩, t, N.normalize q⟩, (O.root a).coordinate j, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · exact (hN _ _ q _ ((O.root a).sorted j)) ▸ hq
  · rintro ⟨a, p, hx⟩
    exact O.presentation_mem_support N a p hx

theorem coordinate_presentation (O : Object C S A) (N : NormalForms L)
    (hN : N.Valid C) (a : A) (j : Fin (S.arity (O.root a).tag)) :
    (O.root a).presentation N
      ⟨⟨(O.root a).tag, j⟩, S.coordinateSort (O.root a).tag j,
        N.normalize (.id (S.coordinateSort (O.root a).tag j))⟩ = {(O.root a).coordinate j} := by
  ext y
  constructor
  · rintro ⟨z, hz, hy⟩
    have hz' : z = (O.root a).coordinate j := by
      simpa only [Root.coordinateGraph_self, Set.mem_singleton_iff] using hz
    subst z
    rw [← hN _ _ (.id _) _ ((O.root a).sorted j)] at hy
    exact hy
  · intro hy
    refine ⟨(O.root a).coordinate j, ⟨rfl, rfl⟩, ?_⟩
    rw [← hN _ _ (.id _) _ ((O.root a).sorted j)]
    exact hy

theorem support_generated (O : Object C S A) :
    O.markedObject.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have liftPath : ∀ {y}, Relation.ReflTransGen C.Step y x.val →
      ∀ (hy : y ∈ O.support), y ∈ O.coordinates →
      ⟨x.val, x.property⟩ ∈ O.markedObject.support := by
    intro y hpath hy hc
    have lift : ∀ {z}, Relation.ReflTransGen C.Step y z →
        ∃ t : O.support, t.val = z ∧
          Relation.ReflTransGen O.supportStructure.Step ⟨y, hy⟩ t := by
      intro z hz
      induction hz with
      | refl => exact ⟨⟨y, hy⟩, rfl, .refl⟩
      | @tail z t hp hs ih =>
        obtain ⟨q, hq, hpath⟩ := ih
        obtain ⟨F, hF⟩ := hs
        have ht : t ∈ O.support := C.isClosed_closure O.coordinates F z (hq ▸ q.property) hF
        refine ⟨⟨t, ht⟩, rfl, hpath.tail ⟨F, ?_⟩⟩
        change t ∈ C.func F q.val
        simpa only [hq] using hF
    obtain ⟨t, ht, hpt⟩ := lift hpath
    have he : t = x := Subtype.ext ht
    obtain ⟨a, j, hj⟩ := hc
    refine ⟨⟨y, hy⟩, ?_, he ▸ hpt⟩
    exact ⟨a, j, Subtype.ext hj⟩
  obtain ⟨y, hy, hpath⟩ := x.property
  exact liftPath hpath (C.subset_closure _ hy) hy

end Object
end CCO.FullCode
