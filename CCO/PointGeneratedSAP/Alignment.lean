import CCO.PointGeneratedSAP.Pieces

/-! Real homogeneity aligns entire point-generated objects. The original
full real group, rather than homogeneity of the hidden structure, is used. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V}
variable {O : Original L V H} (C : Interpretation H O)

theorem align (hom : O.Homogeneous) (A : Piece O)
    (f g : A.Embedding Set.univ) :
    ∃ a : O.Aut, ∀ x, C.lift a • f.point x = g.point x := by
  obtain ⟨a,ha⟩ := hom A.realBase A.finite_realBase f.realRestriction g.realRestriction
  refine ⟨a,?_⟩
  intro x
  have hx : x.val ∈ H.closure (Subtype.val '' A.realBase) := A.generated_realBase.symm ▸ x.property
  obtain ⟨_,⟨r,hr,rfl⟩,j,t,ht⟩ := hx
  have hr' : r.val ∈ A.points := hr
  let rr : A.points := ⟨r.val,hr'⟩
  have hfix : C.lift a • f.point rr = g.point rr := by
    have h := congrArg Subtype.val (ha ⟨r,hr⟩)
    exact (C.lift_real a (f.realRestriction.point ⟨r,hr⟩)).trans h
  have htx : (⟨H.eval t r.val,H.eval_mem_closed A.closed t hr'⟩ : A.points) = x := Subtype.ext ht
  rw [← htx, f.eval_eq t rr, g.eval_eq t rr,H.aut_eval,hfix]

namespace Interpretation

/-- The interpreted action retains every original real point, so even its
faithfulness is proved rather than imposed on abstract avoidance. -/
theorem lift_injective : Function.Injective C.lift := by
  intro a b he
  apply Subtype.ext
  apply Equiv.ext
  intro r
  apply Subtype.ext
  have hh := congrArg (fun g : H.Aut => g • r.val) he
  exact (C.lift_real a r).symm.trans (hh.trans (C.lift_real b r))

/-- The image consists exactly of lifts of ORIGINAL automorphisms fixing D.
Its action on expanded points is the original interpreted action. -/
def baseFixer (D : Set O.Real) : Subgroup H.Aut :=
  (fixer O.Aut D).map C.lift

theorem mem_baseFixer_iff (D : Set O.Real) (g : H.Aut) :
    g ∈ C.baseFixer D ↔ ∃ a : O.Aut, (∀ d ∈ D, a • d = d) ∧ C.lift a = g := by
  exact Subgroup.mem_map

/-- Exactly the orbit under the original FULL Aut(M/D), via its canonical lift. -/
def orbitOver (D : Set O.Real) (u : V) : Set V := MulAction.orbit (C.baseFixer D) u

theorem mem_orbitOver_iff (D : Set O.Real) (u v : V) :
    v ∈ C.orbitOver D u ↔
      ∃ a : O.Aut, (∀ d ∈ D, a • d = d) ∧ C.lift a • u = v := by
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨a,ha,hag⟩ := (C.mem_baseFixer_iff D g.val).mp g.property
    exact ⟨a,ha,by rw [hag]; rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨C.lift a,(C.mem_baseFixer_iff D _).mpr ⟨a,ha,rfl⟩⟩,rfl⟩

def PGO : Prop := ∀ (D : Set O.Real), D.Finite → ∀ u,
  u ∉ H.closure (Subtype.val '' D) → (C.orbitOver D u).Infinite

theorem fixes_closure (D : Set O.Real) (g : C.baseFixer D) :
    ∀ u ∈ H.closure (Subtype.val '' D), g • u = u := by
  obtain ⟨a,ha,hag⟩ := (C.mem_baseFixer_iff D g.val).mp g.property
  apply H.closure_fixed g.val
  rintro _ ⟨r,hr,rfl⟩
  rw [← hag,C.lift_real,ha r hr]

end Interpretation

/-- SAP ONLY for complete induced point-generated pieces and full such bases. -/
def AgeSAP (O : Original L V H) : Prop :=
  ∀ (A B D : Piece O) (s : A.Embedding B.points) (t : A.Embedding D.points),
    ∃ (F : Piece O) (l : B.Embedding F.points) (r : D.Embedding F.points),
      (∀ x, l.point ⟨s.point x,s.mem_point x⟩ = r.point ⟨t.point x,t.mem_point x⟩) ∧
      ∀ x y, l.point x = r.point y → ∃ a, s.point a = x.val ∧ t.point a = y.val

end CCO.PointGeneratedSAP
