import CCO.SIR.Positive.Network
import CCO.StrongExact.TriangleFullness
import CCO.RawExact.DiagramReindex

/-!
# The actual complete selected free-span amalgam

The conditional construction uses one joint selector and an explicit triangle
fullness interface. A separate source theorem discharges fullness by ordinary
AP and CCO. Every output colour, including the real diagonal and both ordered
orientations, is read out on the literal finite set of original tagged points.
-/

universe u v w t

namespace CCO.SIR.Positive

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def TriangleFullness : Prop :=
  ∀ {V : Type (max u v)} (D : CompleteDiagram (S := S) V),
    D.TrianglesRealizable → ∃ f : DiagramHom D.diagram, f.IsInjective

theorem triangleFullness_of_homogeneous_CCO
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,0,w} S) :
    TriangleFullness S := by
  intro V D htri
  obtain ⟨f⟩ := (CCO.semanticCCO_change_universe S cco) V D.diagram
    (D.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous H) htri)
  exact ⟨f, f.injective_of_complete D.complete⟩

variable [DecidableEq (Sigma X)]
variable (K : Selectors.ExactCalculus S) (h : Selectors.HereditarySelector S)

private theorem choose_congr {i j : ι} (D E : S.Menu i j)
    (hD : StrongExact.Exact S D) (hE : StrongExact.Exact S E) (heq : D = E) :
    h.choose D hD = h.choose E hE := by
  cases heq
  rfl

noncomputable def selectedAtom (A C : Finset (Sigma X))
    (x y : Sigma X) (hxy : x ≠ y) : S.Atom x.1 y.1 :=
  h.choose (freeMenu S A C x y) (freeMenu_exact S K A C hxy)

theorem selectedAtom_opposite (A C : Finset (Sigma X))
    (x y : Sigma X) (hxy : x ≠ y) :
    selectedAtom S K h A C y x hxy.symm = S.conv (selectedAtom S K h A C x y hxy) := by
  have he := choose_congr S h _ _
    (K.opposite (freeMenu_exact S K A C hxy))
    (freeMenu_exact S K A C hxy.symm) (freeMenu_opposite S A C x y)
  exact he.symm.trans (h.opposite _ _ _)

noncomputable def selectedColour (A C : Finset (Sigma X)) (x y : Sigma X) :
    Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  if hxy : x = y then taggedColour S x y
    else ⟨x.1, y.1, some (selectedAtom S K h A C x y hxy)⟩

/-- Old finite-factor pairs keep their literal full atomic colours. -/
theorem selectedColour_old_pair (A C : Finset (Sigma X)) (x y : Sigma X)
    (hold : freeMenu S A C x y = edgeMenu S x y) :
    selectedColour S K h A C x y = taggedColour S x y := by
  classical
  by_cases hxy : x = y
  · simp only [selectedColour, dite_eq_left hxy]
  · obtain ⟨a, ha⟩ := S.some_colour_of_ne x.2 y.2 hxy
    have hs : selectedAtom S K h A C x y hxy = a := by
      have he := choose_congr S h _ _ (freeMenu_exact S K A C hxy)
        (StrongExact.exact_singleton S a) (hold.trans (edgeMenu_of_colour S ha))
      exact he.trans (h.singleton S a)
    simp only [selectedColour, dite_eq_right hxy, taggedColour, hs, ha]

noncomputable def selectedDiagram (A C F : Finset (Sigma X)) :
    CompleteDiagram (S := S) ↥F where
  diagram := {
    finite_type := inferInstance
    vertexSort := fun x => x.val.1
    edge := fun x y hxy => some (selectedAtom S K h A C x.val y.val
      (fun he => hxy (Subtype.ext he)))
    edge_reverse := by
      intro x y hxy a
      simp only [Option.some.injEq]
      rw [selectedAtom_opposite S K h A C x.val y.val]
      constructor
      · intro ha
        rw [ha]
      · intro ha
        have hh := congrArg S.conv ha
        simpa only [S.conv_invol] using hh
  }
  complete := by
    intro x y hxy
    exact ⟨_, rfl⟩

theorem selectedDiagram_triangles (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A C F : Finset (Sigma X)) :
    (selectedDiagram S K h A C F).TrianglesRealizable := by
  intro x y z hxy hyz hxz a b c ha hb hc
  have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  have hyz' : y.val ≠ z.val := fun he => hyz (Subtype.ext he)
  have hxz' : x.val ≠ z.val := fun he => hxz (Subtype.ext he)
  have ha' : selectedAtom S K h A C x.val y.val hxy' = a := Option.some.inj ha
  have hb' : selectedAtom S K h A C y.val z.val hyz' = b := Option.some.inj hb
  have hc' : selectedAtom S K h A C x.val z.val hxz' = c := Option.some.inj hc
  rw [← ha', ← hb', ← hc']
  exact h.triangle S _ _ _ (freeMenu_exact S K A C hxy')
    (freeMenu_exact S K A C hyz') (freeMenu_exact S K A C hxz')
    (freeMenu_PC S K hPoint hEdge A C hxy' hyz' hxz')

/-- A selected finite amalgam realized in the original actual source, with the
entire prescribed complete colour table retained. No copy is chosen by SAP.
-/
theorem selected_realization (fullness : TriangleFullness S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A C F : Finset (Sigma X)) :
    ∃ f : ↥F → Sigma X, Function.Injective f ∧
      (∀ x, (f x).1 = x.val.1) ∧
      ∀ x y, taggedColour S (f x) (f y) = selectedColour S K h A C x.val y.val := by
  classical
  let D := selectedDiagram S K h A C F
  obtain ⟨f, hf⟩ := fullness D (selectedDiagram_triangles S K h hPoint hEdge A C F)
  refine ⟨f.image, hf, fun _ => rfl, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [selectedColour, dite_eq_left rfl, taggedColour, DiagramHom.image,
      (S.colour_none_iff (f.point x) (f.point x)).mpr rfl,
      (S.colour_none_iff x.val.2 x.val.2).mpr rfl]
    rfl
  · have hval : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    have hc := f.preserves_edge x y hxy
      (selectedAtom S K h A C x.val y.val hval) rfl
    simp only [selectedColour, dite_eq_right hval, taggedColour, DiagramHom.image, hc]
    rfl

end CCO.SIR.Positive
