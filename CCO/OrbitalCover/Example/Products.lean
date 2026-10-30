import CCO.OrbitalCover.Example.Core
import CCO.PositiveWords

/-! Actual three-distinct-point products of the nine-colour source and
the resulting literal positive-word profiles. These computations are a
consistency check; the semantic CCO theorem has its own direct proof. -/
namespace CCO.OrbitalCover.Example

def coordTriangle : CoordColour → CoordColour → CoordColour → Prop
  | some i, some j, c => c = some (i+j)
  | some _, none, c => c = none
  | none, some _, c => c = none
  | none, none, _ => True

theorem coordinate_triple (x y z : ℕ × Bit) :
    coordTriangle (coordinateColour x.1 x.2 y.1 y.2)
      (coordinateColour y.1 y.2 z.1 z.2)
      (coordinateColour x.1 x.2 z.1 z.2) := by
  by_cases hxy : x.1 = y.1 <;> by_cases hyz : y.1 = z.1
  · simp only [coordinateColour,hxy,hyz,ite_eq_left,coordTriangle,hxy.trans hyz]
    congr 1
    rw [add_assoc,← add_assoc y.2 y.2 z.2,CharTwo.add_self_eq_zero,zero_add]
  · have hxz : x.1 ≠ z.1 := fun h => hyz (hxy.symm.trans h)
    simp [coordinateColour,hxy,hyz,hxz,coordTriangle]
  · have hxz : x.1 ≠ z.1 := fun h => hxy (h.trans hyz.symm)
    simp [coordinateColour,hxy,hyz,hxz,coordTriangle]
  · simp [coordinateColour,hxy,hyz,coordTriangle]

/-- Every entry of the displayed one-coordinate table has literal
coordinate witnesses; fresh clone indices will separate the three points. -/
theorem coordTriangle_realized (a b c : CoordColour) (h : coordTriangle a b c) :
    ∃ x y z : ℕ × Bit,
      coordinateColour x.1 x.2 y.1 y.2 = a ∧
      coordinateColour y.1 y.2 z.1 z.2 = b ∧
      coordinateColour x.1 x.2 z.1 z.2 = c := by
  cases a with
  | none =>
    cases b with
    | none =>
      cases c with
      | none => exact ⟨(1,0),(0,0),(2,0),by decide,by decide,by decide⟩
      | some k => exact ⟨(1,0),(0,0),(1,k),by simp [coordinateColour],
          by simp [coordinateColour],by simp [coordinateColour]⟩
    | some j =>
      change c = none at h
      subst c
      exact ⟨(1,0),(0,0),(0,j),by simp [coordinateColour],
        by simp [coordinateColour],by simp [coordinateColour]⟩
  | some i =>
    cases b with
    | none =>
      change c = none at h
      subst c
      exact ⟨(0,i),(0,0),(1,0),by simp [coordinateColour],
        by simp [coordinateColour],by simp [coordinateColour]⟩
    | some j =>
      change c = some (i+j) at h
      subst c
      exact ⟨(0,i),(0,0),(0,j),by simp [coordinateColour],
        by simp [coordinateColour],by simp [coordinateColour]⟩

theorem triangle_iff {i j k : Unit} (a : source.Atom i j)
    (b : source.Atom j k) (c : source.Atom i k) :
    source.Triangle a b c ↔ coordTriangle a.1 b.1 c.1 ∧ coordTriangle a.2 b.2 c.2 := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    have ha := ((colour_some x y a).mp hxy).2
    have hb := ((colour_some y z b).mp hyz).2
    have hc := ((colour_some x z c).mp hxz).2
    constructor
    · simpa only [pattern,Prod.mk.injEq] using
        (show coordTriangle a.1 b.1 c.1 from by
          rw [← congrArg Prod.fst ha,← congrArg Prod.fst hb,← congrArg Prod.fst hc]
          exact coordinate_triple (x.u,x.p) (y.u,y.p) (z.u,z.p))
    · rw [← congrArg Prod.snd ha,← congrArg Prod.snd hb,← congrArg Prod.snd hc]
      exact coordinate_triple (x.v,x.q) (y.v,y.q) (z.v,z.q)
  · rintro ⟨h1,h2⟩
    obtain ⟨x1,y1,z1,ha1,hb1,hc1⟩ := coordTriangle_realized a.1 b.1 c.1 h1
    obtain ⟨x2,y2,z2,ha2,hb2,hc2⟩ := coordTriangle_realized a.2 b.2 c.2 h2
    let x : Point := ⟨x1.1,x2.1,x1.2,x2.2,0⟩
    let y : Point := ⟨y1.1,y2.1,y1.2,y2.2,1⟩
    let z : Point := ⟨z1.1,z2.1,z1.2,z2.2,2⟩
    refine ⟨x,y,z,?_,?_,?_⟩
    · apply (colour_some x y a).mpr
      refine ⟨?_, Prod.ext ha1 ha2⟩
      intro he
      have hh : (0:ℕ) = 1 := congrArg Point.n he
      cases hh
    · apply (colour_some y z b).mpr
      refine ⟨?_, Prod.ext hb1 hb2⟩
      intro he
      have hh : (1:ℕ) = 2 := congrArg Point.n he
      cases hh
    · apply (colour_some x z c).mpr
      refine ⟨?_, Prod.ext hc1 hc2⟩
      intro he
      have hh : (0:ℕ) = 2 := congrArg Point.n he
      cases hh

end CCO.OrbitalCover.Example
