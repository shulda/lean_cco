import CCO.RealHull.Geometry.Algebra
import CCO.StrongExact.TriangleFullness
import CCO.RawExact.DiagramReindex
import Mathlib.Data.Fintype.Option

/-! A complete new point over the WHOLE actual finite anchor, from H+CCO.
The source triangle test is literal; no SAP/fibre globalisation is used. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

theorem triangle_swap_first {a b c : Atom S} (h : S.Triangle a b c) :
    S.Triangle a c b := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  exact ⟨y,x,z,(col_symm S y x).trans hxy,hxz,hyz⟩

theorem triangle_cycle {a b c : Atom S} (h : S.Triangle a b c) :
    S.Triangle b c a := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  exact ⟨y,z,x,hyz,(col_symm S z x).trans hxz,(col_symm S y x).trans hxy⟩

variable [DecidableEq M]

noncomputable def onePointDiagram (A : Finset M) (q : ↥A → Atom S) :
    CompleteDiagram (S := S) (Option ↥A) where
  diagram := {
    finite_type := inferInstance
    vertexSort := fun _ => ()
    edge := fun x y h => match x,y with
      | none,none => False.elim (h rfl)
      | none,some a => some (q a)
      | some a,none => some (q a)
      | some a,some b => col S a.val b.val
    edge_reverse := by
      intro x y h a
      cases x <;> cases y
      · exact False.elim (h rfl)
      · simp only [S.symmetricLoop]
      · simp only [S.symmetricLoop]
      · exact S.colour_swap _ _ _
  }
  complete := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (h rfl)
      | some b => exact ⟨q b,rfl⟩
    | some a =>
      cases y with
      | none => exact ⟨q a,rfl⟩
      | some b =>
        have hval : a.val ≠ b.val := fun he => h (congrArg some (Subtype.ext he))
        exact col_some_of_ne S hval

theorem onePointDiagram_triangles (A : Finset M) (q : ↥A → Atom S)
    (htri : ∀ a b : ↥A, a ≠ b → ∀ c : Atom S,
      col S a.val b.val = some c → S.Triangle (q a) c (q b)) :
    (onePointDiagram S A q).TrianglesRealizable := by
  intro x y z hxy hyz hxz a b c ha hb hc
  cases x with
  | none =>
    cases y with
    | none => exact False.elim (hxy rfl)
    | some y =>
      cases z with
      | none => exact False.elim (hxz rfl)
      | some z =>
        have hay : q y = a := Option.some.inj ha
        have hcz : q z = c := Option.some.inj hc
        rw [← hay,← hcz]
        exact htri y z (fun he => hyz (congrArg some he)) b hb
  | some x =>
    cases y with
    | none =>
      cases z with
      | none => exact False.elim (hyz rfl)
      | some z =>
        have hax : q x = a := Option.some.inj ha
        have hbz : q z = b := Option.some.inj hb
        rw [← hax,← hbz]
        exact triangle_swap_first S (htri x z (fun he => hxz (congrArg some he)) c hc)
    | some y =>
      cases z with
      | none =>
        have hby : q y = b := Option.some.inj hb
        have hcx : q x = c := Option.some.inj hc
        rw [← hby,← hcx]
        exact triangle_cycle S (htri x y (fun he => hxy (congrArg some he)) a ha)
      | some z => exact ⟨x.val,y.val,z.val,ha,hb,hc⟩

variable {G : Type t} [Group G] [MulAction G M]

/-- The new point is realised over the actual displayed anchor, not a copy
of that anchor. The entire anchor is aligned by one original automorphism. -/
theorem onePointExtension (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S)
    (A : Finset M) (q : ↥A → Atom S)
    (htri : ∀ a b : ↥A, a ≠ b → ∀ c : Atom S,
      col S a.val b.val = some c → S.Triangle (q a) c (q b)) :
    ∃ y : M, y ∉ A ∧ ∀ a : ↥A, col S y a.val = some (q a) := by
  classical
  let D := onePointDiagram S A q
  obtain ⟨f⟩ := (CCO.semanticCCO_change_universe S cco) _ D.diagram
    (D.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous H)
      (onePointDiagram_triangles S A q htri))
  let old : ↥A → M := fun a => f.point (some a)
  have hold : ∀ a b : ↥A, col S (old a) (old b) = col S a.val b.val := by
    intro a b
    by_cases hab : a = b
    · subst b
      rw [(col_none S _ _).mpr rfl,(col_none S _ _).mpr rfl]
    · have hval : a.val ≠ b.val := fun he => hab (Subtype.ext he)
      obtain ⟨c,hc⟩ := col_some_of_ne S hval
      exact (f.preserves_edge (some a) (some b)
        (fun he => hab (Option.some.inj he)) c hc).trans hc.symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun a : ↥A => (⟨(),old a⟩ : Sigma (fun _ : Unit => M)))
    (fun a : ↥A => (⟨(),a.val⟩ : Sigma (fun _ : Unit => M))) (by
      intro a b
      change (⟨(),(),col S (old a) (old b)⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)) = _
      rw [hold a b]
      rfl)
  have hgalign (a : ↥A) : g • old a = a.val := congrArg (fun p => p.2) (hg a)
  let y : M := g • f.point none
  have hspoke (a : ↥A) : col S y a.val = some (q a) := by
    have hf := f.preserves_edge none (some a) (by simp) (q a) rfl
    have hinv := col_invariant S H g (f.point none) (old a)
    rw [hgalign a] at hinv
    exact hinv.trans hf
  refine ⟨y,?_,hspoke⟩
  intro hy
  have hh := hspoke ⟨y,hy⟩
  rw [(col_none S y y).mpr rfl] at hh
  cases hh

end CCO.RealHull.Geometry
