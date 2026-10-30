import CCO.FullCode.CodeTransport

universe u v
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v}

def Presentation.identity (N : NormalForms L) {S : RootScheme L} (q : Coordinate S) :
    Presentation N S :=
  ⟨q, S.coordinateSort q.1 q.2, N.normalize (.id _)⟩

theorem Root.identity_presentation {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (N : NormalForms L) (hN : N.Valid C) (q : Coordinate S) :
    r.presentation N (Presentation.identity N q) = r.coordinateGraph q := by
  ext y
  constructor
  · rintro ⟨z, hz, hy⟩
    have hid := hN _ _ (.id (S.coordinateSort q.1 q.2)) z (r.coordinateGraph_sorted q hz)
    change y ∈ (N.form (S.coordinateSort q.1 q.2) (S.coordinateSort q.1 q.2)
      (N.normalize (.id (S.coordinateSort q.1 q.2)))).eval C z at hy
    rw [← hid] at hy
    exact (Set.mem_singleton_iff.mp hy) ▸ hz
  · intro hy
    refine ⟨y, hy, ?_⟩
    change y ∈ (N.form (S.coordinateSort q.1 q.2) (S.coordinateSort q.1 q.2)
      (N.normalize (.id (S.coordinateSort q.1 q.2)))).eval C y
    rw [← hN _ _ (.id (S.coordinateSort q.1 q.2)) y (r.coordinateGraph_sorted q hy)]
    rfl

def Presentation.follow {N : NormalForms L} {S : RootScheme L} (p : Presentation N S)
    (F : L.Func) (h : p.2.1 = L.input F) : Presentation N S :=
  ⟨p.1, L.output F, N.normalize (.app F (h ▸ N.form _ _ p.2.2))⟩

theorem Root.presentation_follow {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (N : NormalForms L) (hN : N.Valid C) (p : Presentation N S)
    (F : L.Func) (h : p.2.1 = L.input F) (y : V) :
    y ∈ r.presentation N (p.follow F h) ↔ ∃ x, x ∈ r.presentation N p ∧ y ∈ C.func F x := by
  cases p with | mk q ts =>
   cases ts with | mk t i =>
    change t = L.input F at h
    subst t
    constructor
    · rintro ⟨z, hz, hy⟩
      have hn := hN _ _ (.app F (N.form _ _ i)) z (r.coordinateGraph_sorted q hz)
      change y ∈ (N.form _ _ (N.normalize (.app F (N.form _ _ i)))).eval C z at hy
      rw [← hn] at hy
      obtain ⟨x, hx, hy⟩ := hy
      exact ⟨x, ⟨z, hz, hx⟩, hy⟩
    · rintro ⟨x, ⟨z, hz, hx⟩, hy⟩
      refine ⟨z, hz, ?_⟩
      change y ∈ (N.form _ _ (N.normalize (.app F (N.form _ _ i)))).eval C z
      rw [← hN _ _ (.app F (N.form _ _ i)) z (r.coordinateGraph_sorted q hz)]
      exact ⟨x, hx, hy⟩

end CCO.FullCode
