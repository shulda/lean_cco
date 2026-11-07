import CCO.OldIdempotentForest.CycleContractionSequence
import CCO.OldIdempotentForest.VisibleBranches
import CCO.GuardedOldSeams.LiftGraphTheta

/-! Typed arc lines glue back onto the EXACT original specified cyclic
enumeration. Every occurrence and successor edge is covered by an actual
consecutive-cut arc. Only shared OLD endpoint values need agree; no fine
cross colours between private interiors are prescribed here. -/

universe u v w p q
namespace CCO.OldIdempotentForest

open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CycleGeometry

namespace CycleGeometry.OrderedCuts

/-- The finite consecutive-cut intervals cover every original index. -/
theorem interval_at {n : Nat} {mark : Nat → Prop} (cuts : OrderedCuts n mark)
    (distance : Nat) (hd : distance < n) :
    ∃ i : Fin cuts.count, cuts.cut i.castSucc ≤ distance ∧ distance < cuts.cut i.succ := by
  classical
  have hex : ∃ j : Nat, distance < cuts.cutAt j := by
    exact ⟨cuts.count,by simpa only [cuts.cutAt_last] using hd⟩
  let next := Nat.find hex
  have hnext : distance < cuts.cutAt next := Nat.find_spec hex
  have hbound : next ≤ cuts.count := Nat.find_min' hex (by simpa only [cuts.cutAt_last] using hd)
  have hpos : 0 < next := by
    by_contra hn
    have hz : next = 0 := by omega
    rw [hz,cuts.cutAt_zero] at hnext
    omega
  have hbefore : cuts.cutAt (next-1) ≤ distance := by
    by_contra hn
    have hlt : distance < cuts.cutAt (next-1) := by omega
    exact Nat.find_min hex (by omega : next-1 < next) hlt
  let i : Fin cuts.count := ⟨next-1,by omega⟩
  refine ⟨i,?_,?_⟩
  · rw [cuts.cutAt_of_le (next-1) (by omega)] at hbefore
    exact hbefore
  · rw [cuts.cutAt_of_le next hbound] at hnext
    have hi : i.succ = (⟨next,by omega⟩ : Fin (cuts.count+1)) := Fin.ext (by dsimp [i]; omega)
    simpa only [hi] using hnext

end CycleGeometry.OrderedCuts

namespace CycleGeometry

private theorem cycleShift_closed_interval_eq {n : Nat} (hn : 0 < n) (start : Fin n)
    {a b : Nat} (ha : a ≤ n) (hb : b ≤ n)
    (heq : cycleShift hn start a = cycleShift hn start b) :
    a = b ∨ (a = 0 ∧ b = n) ∨ (a = n ∧ b = 0) := by
  by_cases han : a = n
  · by_cases hbn : b = n
    · exact Or.inl (han.trans hbn.symm)
    · have hb0 : b = 0 := by
        apply cycleShift_injective_lt hn start b 0 (by omega) hn
        simpa only [han,cycleShift_period,cycleShift_zero] using heq.symm
      exact Or.inr (Or.inr ⟨han,hb0⟩)
  · by_cases hbn : b = n
    · have ha0 : a = 0 := by
        apply cycleShift_injective_lt hn start a 0 (by omega) hn
        simpa only [hbn,cycleShift_period,cycleShift_zero] using heq
      exact Or.inr (Or.inl ⟨ha0,hbn⟩)
    · exact Or.inl (cycleShift_injective_lt hn start a b (by omega) (by omega) heq)

end CycleGeometry

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {P : Type p} {K : Type q} [Finite P] [Finite K]

namespace RootWordGeometry

variable (R : RootWordSystem S P K) (seed : RootWordSeeds S R)
variable {C : (privateBranchSystem R).Cycle} (D : OrderedCycleSequence C)

private def arcOffset (i : Fin D.cuts.count) (d : Fin ((D.arc i).length+1)) : Nat :=
  D.cuts.cut i.castSucc + d.val

private theorem arcOffset_bounds (i : Fin D.cuts.count) (d : Fin ((D.arc i).length+1)) :
    D.cuts.cut i.castSucc ≤ arcOffset R D i d ∧
      arcOffset R D i d ≤ D.cuts.cut i.succ := by
  have hd := d.isLt
  have hlen := D.arc_length i
  have hpositive := D.cuts.adjacent_positive i
  dsimp [arcOffset]
  omega

/-- Distinct cut arcs can meet only at their OLD endpoints. The statement
also includes the original cyclic closing endpoint, without a new root. -/
theorem arc_overlap_endpoints (i j : Fin D.cuts.count)
    (d : Fin ((D.arc i).length+1)) (e : Fin ((D.arc j).length+1))
    (heq : (D.arc i).vertex d = (D.arc j).vertex e) :
    i = j ∨
      ((d.val = 0 ∨ d.val = (D.arc i).length) ∧
        (e.val = 0 ∨ e.val = (D.arc j).length)) := by
  by_cases hij : i = j
  · exact Or.inl hij
  · right
    have hdi := arcOffset_bounds R D i d
    have hej := arcOffset_bounds R D j e
    have hiN := D.cuts.bounds i.succ
    have hjN := D.cuts.bounds j.succ
    have hde := C.vertex.injective heq
    change cycleShift C.positive D.start (arcOffset R D i d) =
      cycleShift C.positive D.start (arcOffset R D j e) at hde
    have hcases := cycleShift_closed_interval_eq C.positive D.start
      (by omega : arcOffset R D i d ≤ C.length)
      (by omega : arcOffset R D j e ≤ C.length) hde
    have hlenI := D.arc_length i
    have hlenJ := D.arc_length j
    have hposI := D.cuts.adjacent_positive i
    have hposJ := D.cuts.adjacent_positive j
    rcases hcases with hs | ⟨h0,hN⟩ | ⟨hN,h0⟩
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hle : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
        have hc := D.cuts.cut.monotone hle
        have hi : arcOffset R D i d = D.cuts.cut i.succ := by omega
        have hj : arcOffset R D j e = D.cuts.cut j.castSucc := by omega
        dsimp [arcOffset] at hi hj
        exact ⟨Or.inr (by omega),Or.inl (by omega)⟩
      · have hle : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; omega
        have hc := D.cuts.cut.monotone hle
        have hj : arcOffset R D j e = D.cuts.cut j.succ := by omega
        have hi : arcOffset R D i d = D.cuts.cut i.castSucc := by omega
        dsimp [arcOffset] at hi hj
        exact ⟨Or.inl (by omega),Or.inr (by omega)⟩
    · dsimp [arcOffset] at h0 hN
      exact ⟨Or.inl (by omega),Or.inr (by omega)⟩
    · dsimp [arcOffset] at h0 hN
      exact ⟨Or.inr (by omega),Or.inl (by omega)⟩

/-- Every ORIGINAL successor edge, including the original closing edge,
is one consecutive step of a computed actual root-to-root arc. -/
theorem original_edge_on_arc (p : Fin C.length) :
    ∃ (i : Fin D.cuts.count) (d : Fin (D.arc i).length),
      (D.arc i).vertex d.castSucc = C.vertex p ∧
      (D.arc i).vertex d.succ = C.vertex (cyclicNext C.positive p) := by
  obtain ⟨distance,hd,hreach⟩ := cycleShift_reaches C.positive D.start p
  obtain ⟨i,hlo,hhi⟩ := D.cuts.interval_at distance hd
  have hlen := D.arc_length i
  have hpositive := D.cuts.adjacent_positive i
  let d : Fin (D.arc i).length := ⟨distance-D.cuts.cut i.castSucc,by omega⟩
  have hoffset : D.cuts.cut i.castSucc + d.val = distance := by dsimp [d]; omega
  refine ⟨i,d,?_,?_⟩
  · rw [D.arc_vertex]
    change C.vertex (cycleShift C.positive D.start (D.cuts.cut i.castSucc + d.val)) = C.vertex p
    rw [hoffset,hreach]
  · rw [D.arc_vertex]
    change C.vertex (cycleShift C.positive D.start (D.cuts.cut i.castSucc + (d.val+1))) = _
    rw [← Nat.add_assoc,hoffset,cycleShift_succ,hreach]

/-- Typed point data for the exact actual arcs. Values at shared OLD
roots are read from one root assignment, including the closing root. -/
structure CycleArcPoints where
  rootPoint : ∀ r : P, X (R.sort r)
  point : ∀ (i : Fin D.cuts.count) (d : Fin ((D.arc i).length+1)),
    X (R.vertexSort ((D.arc i).vertex d))
  first_image : ∀ i,
    (⟨R.vertexSort ((D.arc i).vertex 0),point i 0⟩ : Sigma X) =
      ⟨R.sort (D.root i.castSucc),rootPoint (D.root i.castSucc)⟩
  last_image : ∀ i,
    (⟨R.vertexSort ((D.arc i).vertex (Fin.last (D.arc i).length)),
      point i (Fin.last (D.arc i).length)⟩ : Sigma X) =
      ⟨R.sort (D.root i.succ),rootPoint (D.root i.succ)⟩
  preserves_step : ∀ (i : Fin D.cuts.count) (d : Fin (D.arc i).length)
    (hne : (D.arc i).vertex d.castSucc ≠ (D.arc i).vertex d.succ)
    (a : S.Atom (R.vertexSort ((D.arc i).vertex d.castSucc))
      (R.vertexSort ((D.arc i).vertex d.succ))),
    (R.diagram seed).edge ((D.arc i).vertex d.castSucc) ((D.arc i).vertex d.succ) hne = some a →
      S.colour (point i d.castSucc) (point i d.succ) = some a

namespace CycleArcPoints

variable {R seed D} (lines : CycleArcPoints R seed D)

private theorem endpoint_image (i : Fin D.cuts.count) (d : Fin ((D.arc i).length+1))
    (hd : d.val = 0 ∨ d.val = (D.arc i).length) :
    ∃ r : P, (D.arc i).vertex d = Sum.inl r ∧
      (⟨R.vertexSort ((D.arc i).vertex d),lines.point i d⟩ : Sigma X) =
        ⟨R.sort r,lines.rootPoint r⟩ := by
  rcases hd with hd | hd
  · have hz : d = 0 := Fin.ext hd
    subst d
    exact ⟨D.root i.castSucc,(D.arc i).first,lines.first_image i⟩
  · have hz : d = Fin.last (D.arc i).length := Fin.ext hd
    subst d
    exact ⟨D.root i.succ,(D.arc i).last,lines.last_image i⟩

/-- Any two ways to cover one original cycle vertex give the same typed
real value. Private occurrences use arc injectivity; overlaps use OLD roots. -/
theorem overlap_image (i j : Fin D.cuts.count)
    (d : Fin ((D.arc i).length+1)) (e : Fin ((D.arc j).length+1))
    (heq : (D.arc i).vertex d = (D.arc j).vertex e) :
    (⟨R.vertexSort ((D.arc i).vertex d),lines.point i d⟩ : Sigma X) =
      ⟨R.vertexSort ((D.arc j).vertex e),lines.point j e⟩ := by
  rcases arc_overlap_endpoints R D i j d e heq with hij | ⟨hd,he⟩
  · subst j
    have hde := (D.arc i).vertex.injective heq
    subst e
    rfl
  · obtain ⟨r,hr,hpoint⟩ := lines.endpoint_image i d hd
    obtain ⟨s,hs,hpoint'⟩ := lines.endpoint_image j e he
    have hrs : r = s := Sum.inl.inj (hr.symm.trans (heq.trans hs))
    subst s
    exact hpoint.trans hpoint'.symm

private structure VertexWitness (p : Fin C.length) where
  index : Fin D.cuts.count
  position : Fin ((D.arc index).length+1)
  vertex_eq : (D.arc index).vertex position = C.vertex p

private theorem vertexWitness_exists (p : Fin C.length) :
    Nonempty (VertexWitness (D := D) p) := by
  obtain ⟨i,d,heq,_⟩ := original_edge_on_arc R D p
  exact ⟨⟨i,d.castSucc,heq⟩⟩

private noncomputable def vertexWitness (p : Fin C.length) : VertexWitness (D := D) p :=
  Classical.choice (vertexWitness_exists (R := R) p)

/-- The point at each ORIGINAL cycle position, without changing its
cyclic enumeration or choosing replacement edges. -/
noncomputable def gluedPoint (p : Fin C.length) : X (R.vertexSort (C.vertex p)) :=
  let witness := vertexWitness (R := R) (D := D) p
  Eq.mp (congrArg X (congrArg R.vertexSort witness.vertex_eq))
    (lines.point witness.index witness.position)

private theorem sigma_forward_cast {s t : ι} (h : s = t) (x : X s) :
    (⟨t,Eq.mp (congrArg X h) x⟩ : Sigma X) = ⟨s,x⟩ := by
  cases h
  rfl

theorem gluedPoint_agrees (p : Fin C.length)
    (i : Fin D.cuts.count) (d : Fin ((D.arc i).length+1))
    (heq : (D.arc i).vertex d = C.vertex p) :
    (⟨R.vertexSort (C.vertex p),lines.gluedPoint p⟩ : Sigma X) =
      ⟨R.vertexSort ((D.arc i).vertex d),lines.point i d⟩ := by
  let witness := vertexWitness (R := R) (D := D) p
  have hcast : (⟨R.vertexSort (C.vertex p),lines.gluedPoint p⟩ : Sigma X) =
      ⟨R.vertexSort ((D.arc witness.index).vertex witness.position),
        lines.point witness.index witness.position⟩ :=
    sigma_forward_cast (congrArg R.vertexSort witness.vertex_eq) _
  exact hcast.trans (lines.overlap_image _ _ _ _ (witness.vertex_eq.trans heq.symm))

private theorem colour_of_equal_vertex_images {s t s' t' : R.Vertex}
    (hs : s = s') (ht : t = t')
    (x : X (R.vertexSort s)) (y : X (R.vertexSort t))
    (x' : X (R.vertexSort s')) (y' : X (R.vertexSort t'))
    (hx : (⟨R.vertexSort s,x⟩ : Sigma X) = ⟨R.vertexSort s',x'⟩)
    (hy : (⟨R.vertexSort t,y⟩ : Sigma X) = ⟨R.vertexSort t',y'⟩)
    (hpres : ∀ (hne : s' ≠ t') (a : S.Atom (R.vertexSort s') (R.vertexSort t')),
      (R.diagram seed).edge s' t' hne = some a → S.colour x' y' = some a)
    (hne : s ≠ t) (a : S.Atom (R.vertexSort s) (R.vertexSort t))
    (ha : (R.diagram seed).edge s t hne = some a) : S.colour x y = some a := by
  cases hs
  cases ht
  have hx' : x = x' := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hx
  have hy' : y = y' := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hy
  rw [hx',hy']
  exact hpres hne a ha

/-- Every ORIGINAL specified successor-edge atom is preserved, including
the original closing edge. No homomorphism of any extra branch is required. -/
theorem gluedPoint_preserves (p : Fin C.length)
    (hne : C.vertex p ≠ C.vertex (cyclicNext C.positive p))
    (a : S.Atom (R.vertexSort (C.vertex p))
      (R.vertexSort (C.vertex (cyclicNext C.positive p))))
    (ha : (R.diagram seed).edge (C.vertex p) (C.vertex (cyclicNext C.positive p)) hne = some a) :
    S.colour (lines.gluedPoint p) (lines.gluedPoint (cyclicNext C.positive p)) = some a := by
  obtain ⟨i,d,hs,ht⟩ := original_edge_on_arc R D p
  exact colour_of_equal_vertex_images (seed := seed) hs.symm ht.symm _ _ _ _
    (lines.gluedPoint_agrees p i d.castSucc hs)
    (lines.gluedPoint_agrees _ i d.succ ht)
    (lines.preserves_step i d) hne a ha

/-- Readback at any actual OLD root occurrence is the same original root
assignment, independently of the chosen covering arc. -/
theorem gluedPoint_root_image (p : Fin C.length) (r : P) (hp : C.vertex p = Sum.inl r) :
    (⟨R.vertexSort (C.vertex p),lines.gluedPoint p⟩ : Sigma X) =
      ⟨R.sort r,lines.rootPoint r⟩ := by
  obtain ⟨i,d,hs,_⟩ := original_edge_on_arc R D p
  have hbound := d.castSucc.isLt
  have hd : d.castSucc.val = 0 ∨ d.castSucc.val = (D.arc i).length := by
    by_cases hz : d.castSucc.val = 0
    · exact Or.inl hz
    · right
      by_contra hlast
      exact (D.arc i).no_internal_root d.castSucc (by omega) (by omega) r (hs.trans hp)
  obtain ⟨s,hroot,hpoint⟩ := lines.endpoint_image i d.castSucc hd
  have hsr : s = r := Sum.inl.inj (hroot.symm.trans (hs.trans hp))
  subst s
  exact (lines.gluedPoint_agrees p i d.castSucc hs).trans hpoint

end CycleArcPoints

/-- Exact cycle walk reconstruction on the original finite cyclic
enumeration. This is a proved local-to-whole gluing theorem, not a supplied
contraction or completion provider. -/
theorem reconstruct_original_cycle_walk (lines : CycleArcPoints R seed D) :
    ∃ point : ∀ p : Fin C.length, X (R.vertexSort (C.vertex p)),
      ∀ (p : Fin C.length) (hne : C.vertex p ≠ C.vertex (cyclicNext C.positive p))
        (a : S.Atom (R.vertexSort (C.vertex p))
          (R.vertexSort (C.vertex (cyclicNext C.positive p)))),
        (R.diagram seed).edge (C.vertex p) (C.vertex (cyclicNext C.positive p)) hne = some a →
          S.colour (point p) (point (cyclicNext C.positive p)) = some a :=
  ⟨lines.gluedPoint,lines.gluedPoint_preserves⟩

end RootWordGeometry
end CCO.OldIdempotentForest
