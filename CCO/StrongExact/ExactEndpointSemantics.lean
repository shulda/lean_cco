import CCO.StrongExact.ThetaFamilySemantics

/-!
# Exact survivor semantics for every finite positive-word menu

Once a common diversity atom is GIVEN, original pair homogeneity realizes
all its positive words over any prescribed pair carrying that atom. The
literal private lines give an actual theta homomorphism. SAP injectivizes
it while fixing both already-distinct roots, so every menu atom is attained
in a strong completion of the SAME finite diagram. This proof uses no
Helly premise and hence is independent of the CCO cycle argument.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

private theorem endpoint_cast_of_sigma_eq {s t : ι} (h : s = t)
    (x : X s) (y : X t)
    (hc : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩) : h ▸ x = y := by
  cases hc
  rfl

/-- Any other common-root family of the SAME original words gives a
homomorphism of the fixed seed diagram. This proves that its endpoint
survivors do not depend on the arbitrary seed realization. -/
noncomputable def thetaHomBetweenLiteralLines
    (ws : List (PositiveWord S i j))
    (x : X i) (y : X j)
    (seed : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
    (x' : X i) (y' : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x' y') :
    DiagramHom ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram) where
  point := thetaFamilyLinePoint S ws x' y' lines
  preserves_edge := by
    classical
    intro z t hzt a ha
    let point := thetaFamilyLinePoint S ws x' y' lines
    have hBranch : ∀ (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)),
        ThetaPairPreserves S
          ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram) point
          (thetaBranchEdgeSource S ws b e) (thetaBranchEdgeTarget S ws b e) := by
      intro b e hne old hOld
      have hForward := thetaEdgesOfLiteralLines_forward S ws x y seed b e
      have hAtom : old = thetaBranchEdgeAtom S ws b e :=
        Option.some.inj (hOld.symm.trans hForward)
      subst old
      exact thetaFamilyLinePoint_letter S ws x' y' lines b e
    have hAdj : thetaAdjacent S ws z t := by
      change (if thetaAdjacent S ws z t then
        S.colour (thetaFamilyLinePoint S ws x y seed z)
          (thetaFamilyLinePoint S ws x y seed t) else none) = some a at ha
      by_contra hNo
      simp [hNo] at ha
    obtain ⟨arc,hArc,hz,ht⟩ := hAdj
    obtain ⟨b,e,hForward | hReverse⟩ :=
      thetaArc_endpoints_on_branch S ws arc hArc
    · have hSource : z = thetaBranchEdgeSource S ws b e :=
        hz.symm.trans hForward.1
      have hTarget : t = thetaBranchEdgeTarget S ws b e :=
        ht.symm.trans hForward.2
      have hPair : ThetaPairPreserves S
          ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram) point z t := by
        rw [hSource,hTarget]
        exact hBranch b e
      exact hPair hzt a ha
    · have hTarget : z = thetaBranchEdgeTarget S ws b e :=
        hz.symm.trans hReverse.1
      have hSource : t = thetaBranchEdgeSource S ws b e :=
        ht.symm.trans hReverse.2
      have hPair : ThetaPairPreserves S
          ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram) point z t := by
        rw [hTarget,hSource]
        exact thetaPairPreserves_reverse S
          ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram) point (hBranch b e)
      exact hPair hzt a ha

/-- Every atom of the presented menu occurs on the two distinct roots
of an injective completion of the fixed seed theta diagram. -/
theorem present_atom_survives_theta_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (x : X i) (y : X j)
    (seed : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
    (a : S.Atom i j) (ha : a ∈ present S ws) :
    a ∈ ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram).survivor
      (thetaLeft S ws) (thetaRight S ws) (thetaLeft_ne_right S ws) := by
  classical
  obtain ⟨x',y',hxy⟩ := S.realized a
  let lines (b : Fin ws.length) : LiteralLine S (ws.get b) x' y' :=
    LiteralLine.of_represented S (ws.get b) x' y'
      (profile_realizes_prescribed_pair_of_SAP S H sap (ws.get b) a
        (ha (ws.get b) (List.get_mem ws b)) x' y' hxy)
  let D := (thetaEdgesOfLiteralLines S ws x y seed).toDiagram
  let f : DiagramHom D := thetaHomBetweenLiteralLines S ws x y seed x' y' lines
  have hRoots : f.image (thetaLeft S ws) ≠ f.image (thetaRight S ws) := by
    change (⟨i,x'⟩ : Sigma X) ≠ ⟨j,y'⟩
    exact S.atomRel_ne hxy
  have hBase : ∀ u ∈ ({thetaLeft S ws,thetaRight S ws} : Set (thetaVertices S ws)),
      ∀ v ∈ ({thetaLeft S ws,thetaRight S ws} : Set (thetaVertices S ws)),
      f.image u = f.image v → u = v := by
    intro u hu v hv he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact False.elim (hRoots he)
    · exact False.elim (hRoots he.symm)
    · rfl
  obtain ⟨g,hg,hKeep⟩ := D.strongCompletion_fixed_base_of_SAP H sap f
    {thetaLeft S ws,thetaRight S ws} hBase
  have hLeft : g.point (thetaLeft S ws) = x' := by
    have hh := hKeep (thetaLeft S ws) (by simp)
    change (⟨i,g.point (thetaLeft S ws)⟩ : Sigma X) = ⟨i,x'⟩ at hh
    exact endpoint_cast_of_sigma_eq rfl _ _ hh
  have hRight : g.point (thetaRight S ws) = y' := by
    have hh := hKeep (thetaRight S ws) (by simp)
    change (⟨j,g.point (thetaRight S ws)⟩ : Sigma X) = ⟨j,y'⟩ at hh
    exact endpoint_cast_of_sigma_eq rfl _ _ hh
  refine ⟨g,hg,?_⟩
  change S.colour (g.point (thetaLeft S ws)) (g.point (thetaRight S ws)) = some a
  rw [hLeft,hRight]
  exact hxy

/-- The survivor menu equals the ORIGINAL evaluated presentation,
including the empty family and compatible duplicate direct branches. -/
theorem theta_survivor_eq_present_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (x : X i) (y : X j)
    (seed : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y) :
    ((thetaEdgesOfLiteralLines S ws x y seed).toDiagram).survivor
      (thetaLeft S ws) (thetaRight S ws) (thetaLeft_ne_right S ws) =
      present S ws := by
  ext a
  constructor
  · rintro ⟨f,_hf,hColour⟩ word hw
    exact (positive_profile_iff_represented S H sap word a).mpr
      ⟨f.point (thetaLeft S ws),f.point (thetaRight S ws),
        thetaEdgesOfLiteralLines_representsWords S ws x y seed f word hw,hColour⟩
  · intro ha
    exact present_atom_survives_theta_of_SAP S H sap ws x y seed a ha

/-- Every nonempty original exact menu is precisely the survivor set
between two distinct formal roots of one finite strongly completable
private-word diagram. Every one of its atoms is attained in that SAME
diagram. SAP is sufficient once the menu is known to be nonempty. -/
theorem exact_menu_survivor_representation_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {A : S.Menu i j} (hA : Exact S A) :
    ∃ (ws : List (PositiveWord S i j)) (T : ThetaEdges S ws),
      T.toDiagram.HasStrongCompletion ∧
      T.toDiagram.survivor (thetaLeft S ws) (thetaRight S ws)
        (thetaLeft_ne_right S ws) = A ∧ T.RepresentsWords := by
  classical
  obtain ⟨hNonempty,ws,hPresentation⟩ := hA
  obtain ⟨a,ha⟩ := hNonempty
  rw [hPresentation] at ha
  obtain ⟨x,y,hxy⟩ := S.realized a
  let seed (b : Fin ws.length) : LiteralLine S (ws.get b) x y :=
    LiteralLine.of_represented S (ws.get b) x y
      (profile_realizes_prescribed_pair_of_SAP S H sap (ws.get b) a
        (ha (ws.get b) (List.get_mem ws b)) x y hxy)
  let T := thetaEdgesOfLiteralLines S ws x y seed
  have hAtom := present_atom_survives_theta_of_SAP S H sap ws x y seed a ha
  obtain ⟨f,hf,_hColour⟩ := hAtom
  refine ⟨ws,T,⟨f,hf⟩,?_,?_⟩
  · exact (theta_survivor_eq_present_of_SAP S H sap ws x y seed).trans
      hPresentation.symm
  · exact thetaEdgesOfLiteralLines_representsWords S ws x y seed

end CCO.StrongExact
