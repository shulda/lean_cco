import CCO.UnaryFreshFrames.SAPFresh

/-! C11–C15: one simultaneous action-avoidance move builds the actual
closed induced union. Its arbitrary cross relations come from H, so this
is strong amalgamation without a claim of free relational amalgamation. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

theorem ageSAP_of_infiniteClosedOrbits (hom : H.Homogeneous)
    (hInf : H.InfiniteClosedOrbits H.Aut) : H.AgeSAP := by
  classical
  intro A B C s t
  obtain ⟨g₀, hg₀⟩ := hom A s.ambient t.ambient
  have halign (a : A.points) : g₀ • s.point a = t.point a := hg₀ a
  let root := t.image
  let moved : Set V := (fun z => g₀ • z) '' B.points
  have hmoved : moved.Finite := B.finite.image _
  have hmoving : (moved \ root.points).Finite := hmoved.sdiff
  let moving := hmoving.toFinset
  let forbidden := C.finite.toFinset
  have hOrbit (x : V) (hx : x ∈ moving) :
      (MulAction.orbit (fixer H.Aut root.points) x).Infinite := by
    have hn : x ∉ root.points := (hmoving.mem_toFinset.mp hx).2
    exact hInf root.points root.finite root.closed x hn
  obtain ⟨k, hk⟩ := AclOwners.finite_action_avoidance
    (G := fixer H.Aut root.points) moving forbidden hOrbit
  let g : H.Aut := k.val * g₀
  have hBase (a : A.points) : g • s.point a = t.point a := by
    change (k.val * g₀) • s.point a = t.point a
    rw [mul_smul, halign a]
    exact k.property (t.point a) ⟨a, rfl⟩
  let D : H.Piece := ⟨(fun z => g • z) '' B.points ∪ C.points,
    (B.finite.image _).union C.finite,
    H.closed_union (H.aut_closed_image g B.closed) C.closed⟩
  let l : B.Embedding D.points :=
    ((Piece.Embedding.identity B).mapAut g).restrictTarget
      (fun b => Or.inl ⟨b.val, b.property, rfl⟩)
  let r : C.Embedding D.points := Piece.Embedding.inclusion (fun _ hc => Or.inr hc)
  refine ⟨D, l, r, hBase, ?_⟩
  intro b c hbc
  have hValue : g • b.val = c.val := hbc
  have hIn : g₀ • b.val ∈ root.points := by
    by_contra hnot
    have hMoving : g₀ • b.val ∈ moving := hmoving.mem_toFinset.mpr
      ⟨⟨b.val, b.property, rfl⟩, hnot⟩
    exact hk (g₀ • b.val) hMoving c.val (C.finite.mem_toFinset.mpr c.property)
      (by change k.val • (g₀ • b.val) = c.val
          simpa only [g, mul_smul] using hValue)
  obtain ⟨a, ha⟩ := hIn
  have hs : s.point a = b.val := MulAction.injective g₀ ((halign a).trans ha)
  refine ⟨a, hs, ?_⟩
  have he := hBase a
  rw [hs] at he
  exact he.symm.trans hValue

theorem ageSAP_iff_infiniteClosedOrbits (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) : H.AgeSAP ↔ H.InfiniteClosedOrbits H.Aut :=
  ⟨H.infiniteClosedOrbits_of_ageSAP hfin hom,
    H.ageSAP_of_infiniteClosedOrbits hom⟩

end CCO.UnaryFreshFrames.Structure
