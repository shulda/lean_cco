import CCO.Injectivization

/-! The source13 clone step uses the COMPLETE set of other ACTUAL old
images. All formal positions with the collided image contribute only ONE
excluded actual point. Every prior clone and every distinct anchor is in
the fixed base. This refines the general diversity-neighbour SAP repair. -/
universe u v w
namespace CCO.HiddenSAPReadings.CompleteBaseClones
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource ι X}
variable {V : Type w} {D : PartialDiagram S V}
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

theorem fresh_move (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f : DiagramHom D) (x : V) (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ f' : DiagramHom D,
      f'.image x ∉ Z ∪ Set.range f.image ∧
      (∀ y : V, y ≠ x → f'.image y = f.image y) := by
  letI : Finite V := D.finite_type
  let B : FiniteInduced (X := X) :=
    ⟨Set.range f.image \ {f.image x},(Set.finite_range _).sdiff⟩
  have hx : f.image x ∉ B.vertices := fun h => h.2 rfl
  obtain ⟨p,⟨g,hg,hgp⟩,hp⟩ := RealAction.orbit_has_fresh_point_of_SAP S H sap B
    (f.image x) hx (Z ∪ Set.range f.image) (hZ.union (Set.finite_range _))
  have hFix (y : V) (hne : f.image y ≠ f.image x) : g • f.point y = f.point y := by
    have h := (RealAction.mem_pointwiseStabilizer B.vertices g).mp hg
      (f.image y) ⟨⟨y,rfl⟩,hne⟩
    exact sigma_mk_injective h
  have hOut : ∀ y (hxy : x ≠ y) a, D.edge x y hxy = some a → g • f.point y = f.point y := by
    intro y hxy a ha
    exact hFix y (Ne.symm (S.atomRel_ne (f.preserves_edge x y hxy a ha)))
  have hIn : ∀ y (hyx : y ≠ x) a, D.edge y x hyx = some a → g • f.point y = f.point y := by
    intro y hyx a ha
    exact hFix y (S.atomRel_ne (f.preserves_edge y x hyx a ha))
  let f' := DiagramHom.moveOne H f x g hOut hIn
  refine ⟨f',?_,?_⟩
  · have hm : f'.image x = g • f.image x := by
      change (⟨D.vertexSort x,f'.point x⟩ : Sigma X) = ⟨D.vertexSort x,g • f.point x⟩
      rw [DiagramHom.moveOne_at]
    rw [hm,hgp]
    exact hp
  · intro y hyx
    change (⟨D.vertexSort y,f'.point y⟩ : Sigma X) = ⟨D.vertexSort y,f.point y⟩
    rw [DiagramHom.moveOne_away H f x g hOut hIn y hyx]

private def Processed (pins : Set V) (f₀ f : DiagramHom D)
    (Z : Set (Sigma X)) (T : Finset V) : Prop :=
  (∀ s ∈ pins, f.image s = f₀.image s) ∧
    ∀ u ∈ T, f.image u ∉ Z ∧ ∀ v : V, u ≠ v → f.image u ≠ f.image v

private theorem process (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f₀ : DiagramHom D) (pins : Set V) (Z : Set (Sigma X)) (hZ : Z.Finite)
    (T : Finset V) (hT : ∀ u ∈ T, u ∉ pins) :
    ∃ f : DiagramHom D, Processed pins f₀ f Z T := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨f₀,fun _ _ => rfl,by simp⟩
  | @insert x T hx ih =>
    obtain ⟨f,hpin,hDone⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu))
    obtain ⟨f',hNew,hOld⟩ := fresh_move H sap f x Z hZ
    refine ⟨f',?_,?_⟩
    · intro s hs
      exact (hOld s (fun he => hT x (Finset.mem_insert_self _ _) (he ▸ hs))).trans (hpin s hs)
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · refine ⟨fun hz => hNew (Or.inl hz),?_⟩
        intro v hxv he
        exact hNew (Or.inr ⟨v,((he.trans (hOld v hxv.symm))).symm⟩)
      · have hux : u ≠ x := fun he => hx (he ▸ hu)
        have hfu := hOld u hux
        refine ⟨by rw [hfu]; exact (hDone u hu).1,?_⟩
        intro v huv he
        by_cases hvx : v = x
        · subst v
          exact hNew (Or.inr ⟨u,hfu.symm.trans he⟩)
        · exact (hDone u hu).2 v huv (hfu.symm.trans (he.trans (hOld v hvx)))

/-- Finite collision descent, now with the source's complete actual
complement at EVERY step, including the previous fresh clones. -/
theorem injectivize (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f₀ : DiagramHom D) (pins : Set V)
    (hPin : ∀ u ∈ pins, ∀ v ∈ pins, f₀.image u = f₀.image v → u = v)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      (∀ s ∈ pins, f.image s = f₀.image s) ∧ ∀ u ∉ pins, f.image u ∉ Z := by
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite V
  let T := Finset.univ.filter (fun v => v ∉ pins)
  have hT : ∀ u ∈ T, u ∉ pins := fun _ hu => (Finset.mem_filter.mp hu).2
  obtain ⟨f,hfixed,hDone⟩ := process H sap f₀ pins Z hZ T hT
  refine ⟨f,?_,hfixed,?_⟩
  · intro u v he
    by_cases hu : u ∈ pins
    · by_cases hv : v ∈ pins
      · exact hPin u hu v hv ((hfixed u hu).symm.trans (he.trans (hfixed v hv)))
      · by_contra huv
        exact (hDone v (by simp [T,hv])).2 u (Ne.symm huv) he.symm
    · by_contra huv
      exact (hDone u (by simp [T,hu])).2 v huv he
  · intro u hu
    exact (hDone u (by simp [T,hu])).1

end CCO.HiddenSAPReadings.CompleteBaseClones
