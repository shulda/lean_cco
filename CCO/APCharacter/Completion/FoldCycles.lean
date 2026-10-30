import CCO.APCharacter.Completion.FoldCoherence
import CCO.StrongExact.CycleIndexRotation
import CCO.StrongExact.FinLinePath

/-! Literal simple-cycle witnesses after one identity fold. The sole
ambiguous quotient fibre is the selected old pair; it is visited at most
once by a simple cycle. No SAP or marked completion is used. -/
universe u v w z
namespace CCO.APCharacter.Completion
open StrongPC
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V) (f : DiagramHom D)
variable (x y : V) (hxy : x ≠ y) (sameSort : D.vertexSort x = D.vertexSort y)
variable (missing : D.edge x y hxy = none) (bound : IdentityBound D x y)

private theorem identify_unique {a : V} {b : Identified y}
    (hb : b.val ≠ x) (ha : identify x y hxy a = b) : a = b.val := by
  classical
  by_cases hay : a = y
  · subst a
    have h := congrArg Subtype.val ha
    exact False.elim (hb (by simpa only [identify_y] using h.symm))
  · have h := congrArg Subtype.val ha
    simpa only [identify_of_ne x y hxy a hay] using h

private theorem pushed_point_representative (a : Identified y)
    (ha : identify x y hxy a.val = a) :
    pushedPoint D f (identify x y hxy) (fun a => D.vertexSort a.val)
      (fun a => (identify_sorts x y hxy D sameSort a).symm) a.val a ha = f.point a.val := by
  exact eq_of_heq (Sigma.mk.inj (pushedPoint_sigma D f (identify x y hxy)
    (fun a => D.vertexSort a.val)
    (fun a => (identify_sorts x y hxy D sameSort a).symm) a.val a ha)).2

/-- Away from the merged fibre, every new edge has the same literal
original endpoints. The old diagram homomorphism therefore realizes it. -/
theorem fold_edge_unmerged (a b : Identified y) (ha : a.val ≠ x) (hb : b.val ≠ x)
    (hab : a ≠ b) (c : S.Atom (D.vertexSort a.val) (D.vertexSort b.val))
    (hc : (foldDiagram D f x y hxy sameSort missing bound).edge a b hab = some c) :
    S.colour (f.point a.val) (f.point b.val) = some c := by
  letI : Finite V := D.finite_type
  obtain ⟨u,v,hu,hv,_,hcol⟩ := pushDiagram_lift D f (identify x y hxy)
    (fun a => D.vertexSort a.val)
    (fun a => (identify_sorts x y hxy D sameSort a).symm)
    (pushCompatible_of_edgeCoherent D f _ _ _ (identify_edge_coherent D f x y hxy missing bound)) a b hab c hc
  have hu' := identify_unique x y hxy ha hu
  have hv' := identify_unique x y hxy hb hv
  subst u
  subst v
  rw [pushed_point_representative D f x y hxy sameSort a hu,
    pushed_point_representative D f x y hxy sameSort b hv] at hcol
  exact hcol

/-- C25: a simple cycle avoiding the merged vertex has its OLD witness,
with every old atom kept literally and no new endpoint choice. -/
theorem fold_cycle_avoids
    (C : SimpleCycle (foldDiagram D f x y hxy sameSort missing bound))
    (avoids : ∀ p, (C.vertices p).val ≠ x) : CycleHom C := by
  refine ⟨fun p => f.point (C.vertices p).val,?_⟩
  intro p c hc
  exact fold_edge_unmerged D f x y hxy sameSort missing bound
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (avoids p) (avoids _)
    (C.next_ne p) c hc

private noncomputable abbrev Folded := foldDiagram D f x y hxy sameSort missing bound

private structure EdgeLift (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (p : Fin C.length) where
  source : V
  target : V
  source_image : identify x y hxy source = C.vertices p
  target_image : identify x y hxy target = C.vertices (cyclicNext C.length_pos p)
  adjacent : (graph D).Adj source target

private noncomputable def edgeLift
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound)) (p : Fin C.length) :
    EdgeLift D f x y hxy sameSort missing bound C p := by
  letI : Finite V := D.finite_type
  apply Classical.choice
  obtain ⟨c,hc⟩ := C.specified p
  obtain ⟨a,b,ha,hb,hab,_⟩ := pushDiagram_lift D f (identify x y hxy)
    (fun a => D.vertexSort a.val)
    (fun a => (identify_sorts x y hxy D sameSort a).symm)
    (pushCompatible_of_edgeCoherent D f _ _ _ (identify_edge_coherent D f x y hxy missing bound))
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) c hc
  exact ⟨⟨a,b,ha,hb,hab⟩⟩

private def lastPos {A : Type z} {E : PartialDiagram S A} (C : SimpleCycle E) : Fin C.length :=
  ⟨C.length-1,by have hp := C.length_pos; omega⟩

private theorem next_last {A : Type z} {E : PartialDiagram S A} (C : SimpleCycle E) :
    cyclicNext C.length_pos (lastPos C) = ⟨0,C.length_pos⟩ := by
  apply Fin.ext
  change (C.length-1+1)%C.length = 0
  have h : C.length-1+1 = C.length := by have hp := C.length_pos; omega
  rw [h,Nat.mod_self]

private noncomputable def openVertex
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound)) : Fin (C.length+1) → V :=
  Fin.lastCases (edgeLift D f x y hxy sameSort missing bound C (lastPos C)).target
    (fun p => (edgeLift D f x y hxy sameSort missing bound C p).source)

private theorem openVertex_image
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound)) (p : Fin C.length) :
    identify x y hxy (openVertex D f x y hxy sameSort missing bound C p.castSucc) = C.vertices p := by
  simp only [openVertex,Fin.lastCases_castSucc]
  exact (edgeLift D f x y hxy sameSort missing bound C p).source_image

private theorem openVertex_last_image
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound)) :
    identify x y hxy (openVertex D f x y hxy sameSort missing bound C (Fin.last C.length)) =
      C.vertices ⟨0,C.length_pos⟩ := by
  simp only [openVertex,Fin.lastCases_last]
  exact (edgeLift D f x y hxy sameSort missing bound C (lastPos C)).target_image.trans
    (congrArg C.vertices (next_last C))

private theorem cycle_nonzero_unmerged
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (zero : C.vertices ⟨0,C.length_pos⟩ = ⟨x,hxy⟩)
    (p : Fin C.length) (hp : p ≠ ⟨0,C.length_pos⟩) : (C.vertices p).val ≠ x := by
  intro h
  apply hp
  apply C.vertices.injective
  exact (Subtype.ext h).trans zero.symm

private theorem openVertex_adjacent
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (zero : C.vertices ⟨0,C.length_pos⟩ = ⟨x,hxy⟩) (p : Fin C.length) :
    (graph D).Adj (openVertex D f x y hxy sameSort missing bound C p.castSucc)
      (openVertex D f x y hxy sameSort missing bound C p.succ) := by
  classical
  by_cases hp : p.val+1 < C.length
  · let r : Fin C.length := ⟨p.val+1,hp⟩
    have hNext : cyclicNext C.length_pos p = r := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hp
    have hr0 : r ≠ ⟨0,C.length_pos⟩ := by intro h; have := congrArg Fin.val h; dsimp [r] at this; omega
    have hu := cycle_nonzero_unmerged D f x y hxy sameSort missing bound C zero r hr0
    have heT := identify_unique x y hxy (by simpa only [hNext] using hu)
      (edgeLift D f x y hxy sameSort missing bound C p).target_image
    have heS := identify_unique x y hxy hu
      (edgeLift D f x y hxy sameSort missing bound C r).source_image
    have he : (edgeLift D f x y hxy sameSort missing bound C p).target =
        (edgeLift D f x y hxy sameSort missing bound C r).source := by
      rw [heT,heS,hNext]
    have hIndex : p.succ = r.castSucc := Fin.ext rfl
    rw [hIndex]
    simp only [openVertex,Fin.lastCases_castSucc]
    rw [← he]
    exact (edgeLift D f x y hxy sameSort missing bound C p).adjacent
  · have hpLast : p = lastPos C := by apply Fin.ext; dsimp [lastPos]; have hh := p.isLt; omega
    have hsLast : p.succ = Fin.last C.length := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_last]; have hh := p.isLt; omega
    rw [hsLast]
    simp only [openVertex,Fin.lastCases_castSucc,Fin.lastCases_last,hpLast]
    exact (edgeLift D f x y hxy sameSort missing bound C (lastPos C)).adjacent

private theorem openVertex_prefix_injective
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound)) :
    Function.Injective (fun p : Fin C.length => openVertex D f x y hxy sameSort missing bound C p.castSucc) := by
  intro p q h
  apply C.vertices.injective
  rw [← openVertex_image D f x y hxy sameSort missing bound C p,
    ← openVertex_image D f x y hxy sameSort missing bound C q]
  exact congrArg (identify x y hxy) h

private theorem openVertex_injective
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (different : openVertex D f x y hxy sameSort missing bound C 0 ≠
      openVertex D f x y hxy sameSort missing bound C (Fin.last C.length)) :
    Function.Injective (openVertex D f x y hxy sameSort missing bound C) := by
  intro p q he
  by_cases hp : p = Fin.last C.length <;> by_cases hq : q = Fin.last C.length
  · exact hp.trans hq.symm
  · subst p
    obtain ⟨q,rfl⟩ := Fin.exists_castSucc_eq.mpr hq
    have hh := congrArg (identify x y hxy) he
    rw [openVertex_last_image,openVertex_image] at hh
    have hq0 := C.vertices.injective hh
    have hq0' : q = ⟨0,C.length_pos⟩ := hq0.symm
    subst q
    exact False.elim (different he.symm)
  · subst q
    obtain ⟨p,rfl⟩ := Fin.exists_castSucc_eq.mpr hp
    have hh := congrArg (identify x y hxy) he
    rw [openVertex_image,openVertex_last_image] at hh
    have hp0 := C.vertices.injective hh
    subst p
    exact False.elim (different he)
  · obtain ⟨p,rfl⟩ := Fin.exists_castSucc_eq.mpr hp
    obtain ⟨q,rfl⟩ := Fin.exists_castSucc_eq.mpr hq
    exact congrArg Fin.castSucc (openVertex_prefix_injective D f x y hxy sameSort missing bound C he)

private theorem lift_edge_tag
    (a b : V) (u v : Identified y)
    (ha : identify x y hxy a = u) (hb : identify x y hxy b = v)
    (hab : (graph D).Adj a b) (huv : u ≠ v)
    (c : S.Atom (D.vertexSort u.val) (D.vertexSort v.val))
    (hc : (Folded D f x y hxy sameSort missing bound).edge u v huv = some c)
    (ra : X (D.vertexSort a)) (rb : X (D.vertexSort b))
    (hReal : ∀ h d, D.edge a b h = some d → S.colour ra rb = some d) :
    taggedColour S ⟨D.vertexSort a,ra⟩ ⟨D.vertexSort b,rb⟩ =
      ⟨D.vertexSort u.val,D.vertexSort v.val,some c⟩ := by
  letI : Finite V := D.finite_type
  cases ha
  cases hb
  let compatible := pushCompatible_of_edgeCoherent D f (identify x y hxy)
    (fun a => D.vertexSort a.val) (fun a => (identify_sorts x y hxy D sameSort a).symm)
    (identify_edge_coherent D f x y hxy missing bound)
  obtain ⟨d,hd,hProjected⟩ := pushDiagram_old_edge D f (identify x y hxy)
    (fun a => D.vertexSort a.val) (fun a => (identify_sorts x y hxy D sameSort a).symm)
    compatible hab huv
  have hdc : d = c := Option.some.inj (hd.symm.trans hc)
  subst d
  have hTag := pushedEdge_tag D f (identify x y hxy)
    (fun a => D.vertexSort a.val) (fun a => (identify_sorts x y hxy D sameSort a).symm)
    _ _ c a b rfl rfl hProjected
  have hOld : taggedColour S ⟨D.vertexSort a,ra⟩ ⟨D.vertexSort b,rb⟩ =
      taggedColour S (f.image a) (f.image b) := by
    obtain ⟨hne,d,hd⟩ := hab
    change (⟨D.vertexSort a,D.vertexSort b,S.colour ra rb⟩ : Σ i, Σ j, Option (S.Atom i j)) = _
    unfold taggedColour DiagramHom.image
    rw [hReal hne d hd,f.preserves_edge a b hne d hd]
  exact hOld.trans hTag

private def castPoint {i j : ι} (h : i = j) (a : X i) : X j := h ▸ a
private theorem castPoint_sigma {i j : ι} (h : i = j) (a : X i) :
    (⟨j,castPoint h a⟩ : Sigma X) = ⟨i,a⟩ := by cases h; rfl

private theorem cycleHom_of_open_realizer
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (zero : C.vertices ⟨0,C.length_pos⟩ = ⟨x,hxy⟩)
    (real : ∀ p : Fin (C.length+1), X (D.vertexSort (openVertex D f x y hxy sameSort missing bound C p)))
    (edges : ∀ (p : Fin C.length) h c,
      D.edge (openVertex D f x y hxy sameSort missing bound C p.castSucc)
        (openVertex D f x y hxy sameSort missing bound C p.succ) h = some c →
      S.colour (real p.castSucc) (real p.succ) = some c)
    (closed : (⟨D.vertexSort (openVertex D f x y hxy sameSort missing bound C 0),real 0⟩ : Sigma X) =
      ⟨D.vertexSort (openVertex D f x y hxy sameSort missing bound C (Fin.last C.length)),real (Fin.last C.length)⟩) :
    CycleHom C := by
  let point : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p).val) := fun p =>
    castPoint ((identify_sorts x y hxy D sameSort _).symm.trans
      (congrArg (fun a : Identified y => D.vertexSort a.val)
        (openVertex_image D f x y hxy sameSort missing bound C p))) (real p.castSucc)
  have pointSigma (p : Fin C.length) :
      (⟨D.vertexSort (C.vertices p).val,point p⟩ : Sigma X) =
      ⟨D.vertexSort (openVertex D f x y hxy sameSort missing bound C p.castSucc),real p.castSucc⟩ :=
    castPoint_sigma _ _
  have nextSigma (p : Fin C.length) :
      (⟨D.vertexSort (C.vertices (cyclicNext C.length_pos p)).val,point (cyclicNext C.length_pos p)⟩ : Sigma X) =
      ⟨D.vertexSort (openVertex D f x y hxy sameSort missing bound C p.succ),real p.succ⟩ := by
    rw [pointSigma]
    by_cases hp : p.val+1 < C.length
    · have he : (cyclicNext C.length_pos p).castSucc = p.succ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hp
      rw [he]
    · have hNext : cyclicNext C.length_pos p = ⟨0,C.length_pos⟩ := by
        apply Fin.ext
        have hh : p.val+1 = C.length := by have hh := p.isLt; omega
        simp [cyclicNext,hh]
      have hLast : p.succ = Fin.last C.length := by
        apply Fin.ext
        simp only [Fin.val_succ,Fin.val_last]
        have hh := p.isLt
        omega
      rw [hNext,hLast]
      exact closed
  refine ⟨point,?_⟩
  intro p c hc
  have hTag := lift_edge_tag D f x y hxy sameSort missing bound
    (openVertex D f x y hxy sameSort missing bound C p.castSucc)
    (openVertex D f x y hxy sameSort missing bound C p.succ)
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
    (openVertex_image D f x y hxy sameSort missing bound C p)
    (by
      have hi := openVertex_last_image D f x y hxy sameSort missing bound C
      by_cases hp : p.val+1 < C.length
      · have he : p.succ = (cyclicNext C.length_pos p).castSucc := by
          apply Fin.ext
          exact (Nat.mod_eq_of_lt hp).symm
        rw [he]
        exact openVertex_image D f x y hxy sameSort missing bound C _
      · have hpLast : p = lastPos C := by apply Fin.ext; dsimp [lastPos]; have hh := p.isLt; omega
        subst p
        have he : (lastPos C).succ = Fin.last C.length := by apply Fin.ext; dsimp [lastPos]; have hh := C.length_pos; omega
        rw [he,next_last]
        exact hi)
    (openVertex_adjacent D f x y hxy sameSort missing bound C zero p)
    (C.next_ne p) c hc (real p.castSucc) (real p.succ) (edges p)
  have hh := (congrArg₂ (taggedColour S) (pointSigma p) (nextSigma p)).trans hTag
  have h1 := eq_of_heq (Sigma.mk.inj hh).2
  exact eq_of_heq (Sigma.mk.inj h1).2

private theorem fold_cycle_at_zero
    (boundRev : IdentityBound D y x)
    (C : SimpleCycle (Folded D f x y hxy sameSort missing bound))
    (zero : C.vertices ⟨0,C.length_pos⟩ = ⟨x,hxy⟩) : CycleHom C := by
  classical
  by_cases sameEnd : openVertex D f x y hxy sameSort missing bound C 0 =
      openVertex D f x y hxy sameSort missing bound C (Fin.last C.length)
  · apply cycleHom_of_open_realizer D f x y hxy sameSort missing bound C zero
      (fun p => f.point (openVertex D f x y hxy sameSort missing bound C p))
    · intro p h c hc
      exact f.preserves_edge _ _ h c hc
    · exact congrArg f.image sameEnd
  · rcases C with ⟨length,hThree,hPos,vertices,nextNe,specified⟩
    cases length with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ n =>
        let C : SimpleCycle (Folded D f x y hxy sameSort missing bound) :=
          ⟨n+2,hThree,hPos,vertices,nextNe,specified⟩
        let line : Fin (n+3) ↪ V :=
          ⟨openVertex D f x y hxy sameSort missing bound C,
            openVertex_injective D f x y hxy sameSort missing bound C sameEnd⟩
        have adjacent (p : Fin (n+2)) :
            (graph D).Adj (line p.castSucc) (line p.succ) :=
          openVertex_adjacent D f x y hxy sameSort missing bound C zero p
        let atoms := fun p : Fin (n+2) => edgeAtom D (adjacent p)
        have hEdges (p : Fin (n+2)) :
            D.edge (line p.castSucc) (line p.succ) (lineStepPair line p).ne = some (atoms p) :=
          edgeAtom_spec D (adjacent p)
        have sameImage : identify x y hxy (line 0) =
            identify x y hxy (line (Fin.last (n+2))) :=
          (openVertex_image D f x y hxy sameSort missing bound C ⟨0,hPos⟩).trans
            (openVertex_last_image D f x y hxy sameSort missing bound C).symm
        have endpointBound : IdentityBound D (line 0) (line (Fin.last (n+2))) := by
          rcases (identify_fibres x y hxy _ _).mp sameImage with heq | ⟨ha,hb⟩ | ⟨ha,hb⟩
          · exact False.elim (sameEnd heq)
          · simpa only [ha,hb] using bound
          · simpa only [ha,hb] using boundRev
        obtain ⟨rx,ry,hPath,hNone⟩ := endpointBound
          (simpleSpecifiedLine D (n+1) line atoms hEdges)
        obtain ⟨point,hFirst,hLast,hLetters⟩ :=
          specifiedLinePath_represented_readout D (n+1) line atoms hEdges rx ry hPath
        apply cycleHom_of_open_realizer D f x y hxy sameSort missing bound C zero point
        · intro p h c hc
          have ha : atoms p = c := Option.some.inj ((hEdges p).symm.trans hc)
          rw [← ha]
          exact hLetters p
        · apply (S.colour_none_iff _ _).mp
          change S.colour (point 0) (point (Fin.last (n+2))) = none
          rw [hFirst,hLast]
          exact hNone

/-- C25-C27: EVERY actual simple cycle after the literal two-point fold
has an old-source homomorphism. A cycle through the merged vertex becomes
one closed old cycle or one old simple x-y path with identity endpoint output.
Both orientations are explicit, and are supplied by the SAME identity path
bound in the receiving finite completion procedure. -/
theorem fold_cycleHom
    (boundRev : IdentityBound D y x)
    (C : SimpleCycle (foldDiagram D f x y hxy sameSort missing bound)) : CycleHom C := by
  classical
  by_cases contains : ∃ p, (C.vertices p).val = x
  · obtain ⟨p,hp⟩ := contains
    apply (C.cycleHom_rotate_iff p).mp
    apply fold_cycle_at_zero D f x y hxy sameSort missing bound boundRev (C.rotate p)
    exact Subtype.ext hp
  · exact fold_cycle_avoids D f x y hxy sameSort missing bound C
      (fun p hp => contains ⟨p,hp⟩)

end CCO.APCharacter.Completion
