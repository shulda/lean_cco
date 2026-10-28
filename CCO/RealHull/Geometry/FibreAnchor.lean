import CCO.RealHull.Geometry.FibrePalette

/-! One shared COMPLETE actual anchor attached to a finite partial diagram
of the literal induced fibre palette. The new vertices remain formal and
may collide under a homomorphism. Every prescribed spoke is retained. -/

universe v w z t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)] {V : Type z}

theorem fibre_edge_symm (D : PartialDiagram (fibreSource S A q) V)
    (x y : V) (hxy : x ≠ y) :
    (D.edge x y hxy).map Subtype.val = (D.edge y x hxy.symm).map Subtype.val := by
  cases hc : D.edge x y hxy with
  | none =>
    cases hd : D.edge y x hxy.symm with
    | none => rfl
    | some c =>
      have hh := (D.edge_reverse y x hxy.symm c).mp hd
      change D.edge x y _ = some c at hh
      rw [hc] at hh
      cases hh
  | some c =>
    have hh := (D.edge_reverse x y hxy c).mp hc
    change D.edge y x _ = some c at hh
    rw [hh]

noncomputable def fibreAnchorDiagram (D : PartialDiagram (fibreSource S A q) V) :
    PartialDiagram S (V ⊕ ↥A) where
  finite_type := by
    letI : Finite V := D.finite_type
    letI : Fintype V := Fintype.ofFinite V
    infer_instance
  vertexSort := fun _ => ()
  edge x y hxy := match x,y with
    | .inl x,.inl y => (D.edge x y (fun he => hxy (congrArg Sum.inl he))).map Subtype.val
    | .inl _,.inr a => some (q a)
    | .inr a,.inl _ => some (q a)
    | .inr a,.inr b => col S a.val b.val
  edge_reverse := by
    intro x y h c
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change (D.edge x y _).map Subtype.val = some c ↔
          (D.edge y x _).map Subtype.val = some (S.conv c)
        rw [fibre_edge_symm S A q D x y, S.symmetricLoop]
      | inr a => simp only [S.symmetricLoop]
    | inr a =>
      cases y with
      | inl y => simp only [S.symmetricLoop]
      | inr b => exact S.colour_swap a.val b.val c

theorem fibreAnchor_complete (D : CompleteDiagram (S := fibreSource S A q) V) :
    (fibreAnchorDiagram S A q D.diagram).IsComplete := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      obtain ⟨c,hc⟩ := D.complete x y (fun he => hxy (congrArg Sum.inl he))
      exact ⟨c.val,by change (D.diagram.edge x y _).map Subtype.val = _; rw [hc]; rfl⟩
    | inr a => exact ⟨q a,rfl⟩
  | inr a =>
    cases y with
    | inl y => exact ⟨q a,rfl⟩
    | inr b =>
      exact col_some_of_ne S (fun he => hxy (congrArg Sum.inr (Subtype.ext he)))

variable {G : Type t} [Group G] [MulAction G M]

/-- Align the WHOLE anchor after any homomorphism of the attached diagram.
The returned points are in the actual fibre, and every originally specified
new-new edge has its original full optional colour.
-/
theorem align_fibre_anchor (H : HomogeneousSource S G)
    (D : PartialDiagram (fibreSource S A q) V)
    (f : DiagramHom (fibreAnchorDiagram S A q D)) :
    ∃ point : V → FibreSet S A q,
      (∀ x y (hne : x ≠ y) c, D.edge x y hne = some c →
        col S (point x).val (point y).val = some c.val) ∧
      (f.IsInjective → Function.Injective point) := by
  let old : ↥A → M := fun a => f.point (.inr a)
  have hold (a b : ↥A) : col S (old a) (old b) = col S a.val b.val := by
    by_cases hab : a = b
    · subst b
      rw [(col_none S _ _).mpr rfl,(col_none S _ _).mpr rfl]
    · obtain ⟨c,hc⟩ := col_some_of_ne S (fun he => hab (Subtype.ext he))
      exact (f.preserves_edge (.inr a) (.inr b)
        (fun he => hab (Sum.inr.inj he)) c hc).trans hc.symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun a : ↥A => (⟨(),old a⟩ : Sigma (fun _ : Unit => M)))
    (fun a : ↥A => (⟨(),a.val⟩ : Sigma (fun _ : Unit => M))) (by
      intro a b
      exact congrArg (fun c => (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j))) (hold a b))
  have hgalign (a : ↥A) : g • old a = a.val := congrArg (fun p => p.2) (hg a)
  have hmember (x : V) : g • f.point (.inl x) ∈ FibreSet S A q := by
    intro a
    have hs := f.preserves_edge (.inl x) (.inr a) (by simp) (q a) rfl
    have hi := col_invariant S H g (f.point (.inl x)) (old a)
    rw [hgalign a] at hi
    exact hi.trans hs
  let point : V → FibreSet S A q := fun x => ⟨g • f.point (.inl x),hmember x⟩
  refine ⟨point,?_,?_⟩
  · intro x y hne c hc
    have hf := f.preserves_edge (.inl x) (.inl y)
      (fun he => hne (Sum.inl.inj he)) c.val (by
        change (D.edge x y _).map Subtype.val = some c.val
        rw [hc]
        rfl)
    exact (col_invariant S H g _ _).trans hf
  · intro hf x y hxy
    have hvalues := congrArg Subtype.val hxy
    have hactual : f.point (.inl x) = f.point (.inl y) := MulAction.injective g hvalues
    have hh := hf (congrArg (Sigma.mk ()) hactual)
    exact Sum.inl.inj hh

end CCO.RealHull.Geometry
