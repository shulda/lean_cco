import CCO.SafeReadings.SafeAmalgamation
import CCO.StrongExact.ExactEndpointSemantics
import CCO.StrongExact.ThetaAdjacency

/-! Long positive-path restrictions can be preserved while ONE actual
root edge is recoloured. Every formal theta vertex is first injectivized;
no word edge can therefore become the root pair accidentally. -/
universe u v w z
namespace CCO.SafeReadings
open StrongExact
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]

theorem exact_nonsingleton_presentation_long {i j} {D : S.Menu i j}
    (hD : Exact S D) (hns : ∀ a, D ≠ {a}) :
    ∃ ws : List (PositiveWord S i j), D = present S ws ∧
      ∀ a, (PositiveWord.single a : PositiveWord S i j) ∉ ws := by
  obtain ⟨hne,ws,hw⟩ := hD
  refine ⟨ws,hw,?_⟩
  intro a ha
  apply hns a
  apply Set.Subset.antisymm
  · intro b hb
    rw [hw] at hb
    exact hb (.single a) ha
  · obtain ⟨b,hb⟩ := hne
    have hba : b = a := by
      rw [hw] at hb
      exact Set.mem_singleton_iff.mp (hb (.single a) ha)
    simpa only [hba] using Set.singleton_subset_iff.mpr hb

/-- An actual injective theta witness over a PREASSIGNED literal root
edge, retaining that whole root edge while splitting ALL private points. -/
theorem prescribed_injective_theta (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j} (ws : List (PositiveWord S i j)) (d : S.Atom i j)
    (hd : d ∈ present S ws) (x : X i) (y : X j) (hxy : S.colour x y = some d) :
    ∃ (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
      (f : DiagramHom ((thetaEdgesOfLiteralLines S ws x y lines).toDiagram)),
      f.IsInjective ∧ f.point (thetaLeft S ws) = x ∧ f.point (thetaRight S ws) = y := by
  classical
  let lines (b : Fin ws.length) : LiteralLine S (ws.get b) x y :=
    LiteralLine.of_represented S (ws.get b) x y
      (profile_realizes_prescribed_pair_of_SAP S H sap (ws.get b) d
        (hd _ (List.get_mem ws b)) x y hxy)
  let T := thetaEdgesOfLiteralLines S ws x y lines
  let f := thetaHomOfLiteralLines S ws x y lines
  have hr : f.image (thetaLeft S ws) ≠ f.image (thetaRight S ws) := S.atomRel_ne hxy
  have hpin : ∀ p ∈ ({thetaLeft S ws,thetaRight S ws} : Set (thetaVertices S ws)),
      ∀ q ∈ ({thetaLeft S ws,thetaRight S ws} : Set (thetaVertices S ws)),
      f.image p = f.image q → p = q := by
    intro p hp q hq he
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · exact (hr he).elim
    · exact (hr he.symm).elim
    · rfl
  obtain ⟨g,hg,hkeep⟩ := T.toDiagram.strongCompletion_fixed_base_of_SAP H sap f _ hpin
  refine ⟨lines,g,hg,?_,?_⟩
  · have hh := hkeep (thetaLeft S ws) (by simp)
    change (⟨i,g.point (thetaLeft S ws)⟩ : Sigma X) = ⟨i,x⟩ at hh
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  · have hh := hkeep (thetaRight S ws) (by simp)
    change (⟨j,g.point (thetaRight S ws)⟩ : Sigma X) = ⟨j,y⟩ at hh
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh

/-- Recolour a root edge whilst retaining ALL long path restrictions
and ALL other colours in any prescribed finite set of actual real points. -/
theorem long_presentation_safe_modification
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j} (ws : List (PositiveWord S i j))
    (hlong : ∀ a, (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (d : S.Atom i j) (hd : d ∈ present S ws)
    (x : X i) (y : X j) (hxy : S.colour x y = some d)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ (U : Set (Sigma X)) (_hU : U.Finite)
      (hx : (⟨i,x⟩ : Sigma X) ∈ U) (hy : (⟨j,y⟩ : Sigma X) ∈ U),
      Z ⊆ U ∧ ∃ point : ∀ p : U, X p.val.1,
      Function.Injective (fun p : U => (⟨p.val.1,point p⟩ : Sigma X)) ∧
      (∀ p q : U, ¬ (p.val = ⟨i,x⟩ ∧ q.val = ⟨j,y⟩) →
        ¬ (p.val = ⟨j,y⟩ ∧ q.val = ⟨i,x⟩) →
        S.colour (point p) (point q) = S.colour p.val.2 q.val.2) ∧
      ∃ a ∈ present S ws ∩ safe i j,
        S.colour (point ⟨⟨i,x⟩,hx⟩) (point ⟨⟨j,y⟩,hy⟩) = some a := by
  classical
  obtain ⟨lines,f,hf,hfx,hfy⟩ := prescribed_injective_theta S H sap ws d hd x y hxy
  let D := (thetaEdgesOfLiteralLines S ws x y lines).toDiagram
  have hfl : f.image (thetaLeft S ws) = (⟨i,x⟩ : Sigma X) := by
    change (⟨i,f.point (thetaLeft S ws)⟩ : Sigma X) = _; rw [hfx]
  have hfr : f.image (thetaRight S ws) = (⟨j,y⟩ : Sigma X) := by
    change (⟨j,f.point (thetaRight S ws)⟩ : Sigma X) = _; rw [hfy]
  letI : Finite (thetaVertices S ws) := finite_thetaVertices S ws
  let U : Set (Sigma X) := Set.range f.image ∪ Z
  have hU : U.Finite := (Set.finite_range f.image).union hZ
  letI : Finite U := hU.to_subtype
  have hx : (⟨i,x⟩ : Sigma X) ∈ U := Or.inl ⟨thetaLeft S ws,hfl⟩
  have hy : (⟨j,y⟩ : Sigma X) ∈ U := Or.inl ⟨thetaRight S ws,hfr⟩
  let l : U := ⟨⟨i,x⟩,hx⟩
  let r : U := ⟨⟨j,y⟩,hy⟩
  have hlr : l ≠ r := fun he => S.atomRel_ne hxy (congrArg Subtype.val he)
  obtain ⟨point,hpoint,hkeep,a,ha,hacol⟩ := one_edge_safe_recolour_typed S hs
    (fun p : U => p.val.1) (fun p => p.val.2) Subtype.val_injective l r hlr
  let incl (p : thetaVertices S ws) : U := ⟨f.image p,Or.inl ⟨p,rfl⟩⟩
  have hil : incl (thetaLeft S ws) = l := Subtype.ext hfl
  have hir : incl (thetaRight S ws) = r := Subtype.ext hfr
  have noedge (h : thetaLeft S ws ≠ thetaRight S ws) : D.edge _ _ h = none := by
    change (if thetaAdjacent S ws (thetaLeft S ws) (thetaRight S ws) then _ else none) = _
    exact ite_eq_right (thetaAdjacent_no_root_pair S ws hlong)
  let g : DiagramHom D := {
    point := fun p => point (incl p)
    preserves_edge := by
      intro p q hpq b hb
      have hn1 : ¬ (incl p = l ∧ incl q = r) := by
        rintro ⟨hp,hq⟩
        have hp' : p = thetaLeft S ws := hf ((congrArg Subtype.val hp).trans hfl.symm)
        have hq' : q = thetaRight S ws := hf ((congrArg Subtype.val hq).trans hfr.symm)
        subst p; subst q; rw [noedge hpq] at hb; contradiction
      have hn2 : ¬ (incl p = r ∧ incl q = l) := by
        rintro ⟨hp,hq⟩
        have hp' : p = thetaRight S ws := hf ((congrArg Subtype.val hp).trans hfr.symm)
        have hq' : q = thetaLeft S ws := hf ((congrArg Subtype.val hq).trans hfl.symm)
        subst p; subst q
        have hb' := (D.edge_reverse _ _ hpq b).mp hb
        rw [noedge hpq.symm] at hb'; contradiction
      exact (hkeep (incl p) (incl q) hn1 hn2).trans (f.preserves_edge p q hpq b hb) }
  have gl : g.point (thetaLeft S ws) = point l := by
    have hh := congrArg (fun p : U => (⟨p.val.1,point p⟩ : Sigma X)) hil
    change (⟨i,g.point (thetaLeft S ws)⟩ : Sigma X) = ⟨i,point l⟩ at hh
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  have gr : g.point (thetaRight S ws) = point r := by
    have hh := congrArg (fun p : U => (⟨p.val.1,point p⟩ : Sigma X)) hir
    change (⟨j,g.point (thetaRight S ws)⟩ : Sigma X) = ⟨j,point r⟩ at hh
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  have haWords : a ∈ present S ws := by
    intro word hw
    exact (positive_profile_iff_represented S H sap word a).mpr
      ⟨g.point (thetaLeft S ws),g.point (thetaRight S ws),
        thetaEdgesOfLiteralLines_representsWords S ws x y lines g word hw,
        by rw [gl,gr]; exact hacol⟩
  refine ⟨U,hU,hx,hy,fun _ hz => Or.inr hz,point,hpoint,?_,a,⟨haWords,ha⟩,hacol⟩
  intro p q h1 h2
  exact hkeep p q (fun hh => h1 ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩)
    (fun hh => h2 ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩)

end CCO.SafeReadings
