import CCO.TypedOrbitFrames.CompleteBaseCycleReduction
import CCO.PairHomogeneity
import CCO.StrongGeometry
import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.FinCases

/-!
# Source11 T02: the literal old exact-coloured orbit diagram

The old base is an actual finite injective tuple. Every formal clone has
the complete old one-point type of `q`; only graph edges between clones
receive the chosen diversity atom. Other clone pairs remain unassigned.
-/

namespace CCO.TypedOrbitFrames

universe u v w z t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} {Y : Type t} [Finite B] [Finite Y]
variable (base : B ↪ Sigma X) {i : ι} (q : X i)
variable (K : SimpleGraph Y) (e : S.Atom i i)

/-- The exact old sort of each base point and the fixed clone sort. -/
def originalOrbitSort : B ⊕ Y → ι :=
  Sum.elim (fun d => (base d).1) (fun _ => i)

/-- Literal actual old colours on the complete base and ALL spokes.
Only an edge of the chosen clone graph is prescribed between clones. -/
noncomputable def originalOrbitDiagram : PartialDiagram S (B ⊕ Y) where
  finite_type := inferInstance
  vertexSort := originalOrbitSort base (Y := Y) (i := i)
  edge x y _ := by
    classical
    cases x with
    | inl d =>
      cases y with
      | inl b => exact S.colour (base d).2 (base b).2
      | inr _ => exact S.colour (base d).2 q
    | inr a =>
      cases y with
      | inl d => exact S.colour q (base d).2
      | inr b => exact if K.Adj a b then some e else none
  edge_reverse := by
    classical
    intro x y h a
    cases x with
    | inl d =>
      cases y with
      | inl b => exact S.colour_swap _ _ _
      | inr b => exact S.colour_swap _ _ _
    | inr b =>
      cases y with
      | inl d => exact S.colour_swap _ _ _
      | inr c =>
        change (if K.Adj b c then some e else none) = some a ↔
          (if K.Adj c b then some e else none) = some (S.conv a)
        by_cases he : K.Adj b c
        · simp only [ite_eq_left he, ite_eq_left (K.adj_symm he)]
          rw [show S.conv a = a from S.symmetricLoop (i := i) a]
          rfl
        · have hr : ¬ K.Adj c b := fun hh => he (K.adj_symm hh)
          simp only [ite_eq_right he, ite_eq_right hr, reduceCtorEq]

/-- Each clone has the actual original realised complete one-point type. -/
def originalOrbitTarget : ∀ x : B ⊕ Y,
    X (originalOrbitSort base (Y := Y) (i := i) x) :=
  fun x => match x with
    | .inl d => (base d).2
    | .inr _ => q

/-- The actual distinguished point is outside the old base, so every
spoke is a diversity atom; the full base is complete as well. -/
theorem original_orbit_complete_base_spokes
    (hq : (⟨i,q⟩ : Sigma X) ∉ Set.range base) :
    OriginalCompleteBaseSpokes S (originalOrbitDiagram S base q K e) := by
  intro d x hne
  cases x with
  | inl b =>
    have hdb : base d ≠ base b := fun hh => hne (congrArg Sum.inl (base.injective hh))
    exact S.some_colour_of_ne _ _ hdb
  | inr b =>
    have hdq : base d ≠ (⟨i,q⟩ : Sigma X) := by
      intro hh
      exact hq ⟨d,hh⟩
    exact S.some_colour_of_ne _ _ hdq

/-- An actual STRONG fork through the old anchor, with both spokes
equal to the original spoke of `q`. This is exactly the local content
of membership in `{t_d} ⋆ {converse t_d}`, without a RAW diagonal. -/
def OriginalOrbitForks : Prop :=
  ∀ d : B, ∃ (x z : X i) (y : X (base d).1),
    S.colour x y = S.colour q (base d).2 ∧
    S.colour z y = S.colour q (base d).2 ∧
    S.colour x z = some e

theorem original_orbit_clone_edge_iff (x y : Y)
    (hne : (Sum.inr x : B ⊕ Y) ≠ Sum.inr y) (a : S.Atom i i) :
    (originalOrbitDiagram S base q K e).edge (.inr x) (.inr y) hne = some a ↔
      K.Adj x y ∧ e = a := by
  classical
  change (if K.Adj x y then some e else none) = some a ↔ _
  by_cases h : K.Adj x y <;> simp [h]

/-- Endpoint transport is done on the WHOLE dependent old edge, so its
atom and both sort tags move together. -/
theorem original_orbit_clone_edge_reading
    {x y : B ⊕ Y} {v w : Y} (hx : x = Sum.inr v) (hy : y = Sum.inr w)
    (hne : x ≠ y)
    (a : S.Atom ((originalOrbitDiagram S base q K e).vertexSort x)
      ((originalOrbitDiagram S base q K e).vertexSort y))
    (ha : (originalOrbitDiagram S base q K e).edge x y hne = some a) :
    K.Adj v w ∧ HEq a e := by
  subst x
  subst y
  obtain ⟨hadj,he⟩ := (original_orbit_clone_edge_iff S base q K e v w hne a).mp ha
  exact ⟨hadj,heq_of_eq he.symm⟩

private theorem fork_reverse_colour {j : ι} {x : X i} {y : X j}
    {d : X j} (h : S.colour x y = S.colour q d) :
    S.colour y x = S.colour d q := by
  rw [S.colour_reverse x y, h, ← S.colour_reverse q d]

/-- All displayed triangles are genuinely old triangles. Two base points
use the realised complete old one-point type; one base point uses its
actual STRONG fork. A clone-only triangle is absent from the chosen graph. -/
theorem original_orbit_triangles
    (hfork : OriginalOrbitForks S base q e)
    (hK : ∀ x y z : Y, K.Adj x y → K.Adj y z → ¬ K.Adj x z)
    (x y z : B ⊕ Y) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a : S.Atom ((originalOrbitDiagram S base q K e).vertexSort x)
      ((originalOrbitDiagram S base q K e).vertexSort y))
    (b : S.Atom ((originalOrbitDiagram S base q K e).vertexSort y)
      ((originalOrbitDiagram S base q K e).vertexSort z))
    (c : S.Atom ((originalOrbitDiagram S base q K e).vertexSort x)
      ((originalOrbitDiagram S base q K e).vertexSort z))
    (ha : (originalOrbitDiagram S base q K e).edge x y hxy = some a)
    (hb : (originalOrbitDiagram S base q K e).edge y z hyz = some b)
    (hc : (originalOrbitDiagram S base q K e).edge x z hxz = some c) :
    S.Triangle a b c := by
  cases x with
  | inl d =>
    cases y with
    | inl f =>
      cases z with
      | inl g => exact ⟨(base d).2,(base f).2,(base g).2,ha,hb,hc⟩
      | inr v => exact ⟨(base d).2,(base f).2,q,ha,hb,hc⟩
    | inr v =>
      cases z with
      | inl f => exact ⟨(base d).2,q,(base f).2,ha,hb,hc⟩
      | inr w =>
        obtain ⟨_,he⟩ := (original_orbit_clone_edge_iff S base q K e v w hyz b).mp hb
        obtain ⟨l,r,m,hl,hr,hlr⟩ := hfork d
        exact ⟨m,l,r,(fork_reverse_colour S q hl).trans ha,
          hlr.trans (congrArg some he),(fork_reverse_colour S q hr).trans hc⟩
  | inr v =>
    cases y with
    | inl d =>
      cases z with
      | inl f => exact ⟨q,(base d).2,(base f).2,ha,hb,hc⟩
      | inr w =>
        obtain ⟨_,he⟩ := (original_orbit_clone_edge_iff S base q K e v w hxz c).mp hc
        obtain ⟨l,r,m,hl,hr,hlr⟩ := hfork d
        exact ⟨l,m,r,hl.trans ha,(fork_reverse_colour S q hr).trans hb,
          hlr.trans (congrArg some he)⟩
    | inr w =>
      cases z with
      | inl d =>
        obtain ⟨_,he⟩ := (original_orbit_clone_edge_iff S base q K e v w hxy a).mp ha
        obtain ⟨l,r,m,hl,hr,hlr⟩ := hfork d
        exact ⟨l,r,m,hlr.trans (congrArg some he),hr.trans hb,hl.trans hc⟩
      | inr u =>
        have hvw := ((original_orbit_clone_edge_iff S base q K e v w hxy a).mp ha).1
        have hwu := ((original_orbit_clone_edge_iff S base q K e w u hyz b).mp hb).1
        have hvu := ((original_orbit_clone_edge_iff S base q K e v u hxz c).mp hc).1
        exact False.elim (hK v w u hvw hwu hvu)

/-- A literal triangle cycle is realised by its actual three-vertex
triangle. No arbitrary partial-diagram completion is assumed. -/
theorem original_triangle_cycle_hom_of_triangle
    {V : Type*} (D : PartialDiagram S V) (C : SimpleCycle D)
    (h3 : C.length = 3)
    (htri : ∀ x y z : V, ∀ hxy : x ≠ y, ∀ hyz : y ≠ z,
      ∀ hxz : x ≠ z,
      ∀ a : S.Atom (D.vertexSort x) (D.vertexSort y),
      ∀ b : S.Atom (D.vertexSort y) (D.vertexSort z),
      ∀ c : S.Atom (D.vertexSort x) (D.vertexSort z),
      D.edge x y hxy = some a → D.edge y z hyz = some b →
      D.edge x z hxz = some c → S.Triangle a b c) :
    CycleHom C := by
  rcases C with ⟨n,hge,hpos,vs,hne,hspec⟩
  change n = 3 at h3
  subst n
  obtain ⟨a,ha⟩ := hspec 0
  obtain ⟨b,hb⟩ := hspec 1
  obtain ⟨c,hc⟩ := hspec 2
  have h02 : vs 0 ≠ vs 2 := vs.injective.ne (by decide)
  have h02c := (D.edge_reverse (vs 2) (vs 0) (hne 2) c).mp hc
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ :=
    htri (vs 0) (vs 1) (vs 2) (hne 0) (hne 1) h02
      a b (S.conv c) ha hb h02c
  let point : ∀ p : Fin 3, X (D.vertexSort (vs p)) :=
    Fin.cases x (Fin.cases y (Fin.cases z (fun p => Fin.elim0 p)))
  have hp0 : point 0 = x := rfl
  have hp2 : point 2 = z := by rfl
  refine ⟨point,?_⟩
  intro p atom hatom
  fin_cases p
  · have he : atom = a := Option.some.inj (hatom.symm.trans ha)
    subst atom
    exact hxy
  · have he : atom = b := Option.some.inj (hatom.symm.trans hb)
    subst atom
    exact hyz
  · have he : atom = c := Option.some.inj (hatom.symm.trans hc)
    subst atom
    have hh : S.colour z x = some c :=
      ((S.colour_swap x z (S.conv c)).mp hxz).trans
        (congrArg some (S.conv_invol c))
    simpa [cyclicNext,hp0,hp2] using hh

end CCO.TypedOrbitFrames
