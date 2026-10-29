import CCO.SafeReadings.TransversalSource
import CCO.OwnerTransversal.TransversalExtension
import CCO.StrongExact.CycleCompletion

universe v w t z
namespace CCO.SafeReadings.TransversalSource
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- Each literal source atom has the actual required old owner-pair cap. -/
theorem palette_compatible {i j : ↥B} (a : Palette S H R B i j) :
    ownerSaturate R.E.val (S.atomRel a.val) i.val.out j.val.out := by
  obtain ⟨x,y,hxy⟩ := a.property.2
  obtain ⟨f,ho,hc,_⟩ := TransversalAge.realize_tuple S H R B (![x.val,y.val])
  have hox : owner S H R (f 0).val = i.val :=
    congrArg Subtype.val ((ho 0).trans x.property)
  have hoy : owner S H R (f 1).val = j.val :=
    congrArg Subtype.val ((ho 1).trans y.property)
  have hx : R.E i.val.out (f 0).val := Quotient.exact ((Quotient.out_eq _).trans hox.symm)
  have hy : R.E (f 1).val j.val.out := Quotient.exact (hoy.trans (Quotient.out_eq _).symm)
  exact ⟨(f 1).val,⟨(f 0).val,hx,(hc 0 1).trans hxy⟩,hy⟩

/-- Read an actual typed U triangle in one finite original origin chart. -/
theorem source_triangle_original {i j k : ↥B}
    {a : (source S H R B).Atom i j} {b : (source S H R B).Atom j k}
    {c : (source S H R B).Atom i k}
    (h : (source S H R B).Triangle a b c) : S.Triangle a.val b.val c.val := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  obtain ⟨f,_,hc,_⟩ := TransversalAge.realize_tuple S H R B (![x.val,y.val,z.val])
  exact ⟨(f 0).val,(f 1).val,(f 2).val,
    (hc 0 1).trans ((colour_some_iff S H R B x y a).mp hxy),
    (hc 1 2).trans ((colour_some_iff S H R B y z b).mp hyz),
    (hc 0 2).trans ((colour_some_iff S H R B x z c).mp hxz)⟩

/-- A separated actual origin map embeds in the INTERNALLY constructed U. -/
theorem embed_origin_pattern {V : Type z} [Finite V]
    (P : OriginPattern S H R V) (sort : V → ↥B)
    (hsort : ∀ x, P.owner x = (sort x).val)
    (f : OriginMap S H R B P) (hsep : f.PacketSeparated) :
    ∃ point : ∀ x, Carrier S H R B (sort x),
      Function.Injective (fun x => (point x).val) ∧
      ∀ x y a, P.edge x y = some a →
        (TransversalAge.limitTable S H R B).colour (point x).val (point y).val = some a := by
  obtain ⟨e,ho,hc⟩ := TransversalAge.embed_origins S H R B f.point hsep
  have howner (x) : TransversalAge.ownerLabel S H R B (f.point x) = sort x :=
    Subtype.ext ((f.owner x).trans (hsort x))
  let point : ∀ x, Carrier S H R B (sort x) := fun x => ⟨e x,(ho x).trans (howner x)⟩
  exact ⟨point,e.injective,fun x y a ha => (hc x y).trans (f.edge x y a ha)⟩

/-- Forget only the typed owner tags, retaining every literal fine edge. -/
def pattern {V : Type z} [DecidableEq V] (D : PartialDiagram (source S H R B) V) : OriginPattern S H R V where
  owner x := (D.vertexSort x).val
  edge x y := if h : x = y then none else (D.edge x y h).map Subtype.val
  symmetric := by
    intro x y
    by_cases hxy : x = y
    · subst y; simp
    · simp only [hxy,(Ne.symm hxy),not_false_eq_true,dif_neg]
      cases he : D.edge x y hxy with
      | none =>
        cases hf : D.edge y x (Ne.symm hxy) with
        | none => rfl
        | some b =>
          have hh := (D.edge_reverse y x (Ne.symm hxy) b).mp hf
          rw [he] at hh
          cases hh
      | some a =>
        rw [(D.edge_reverse x y hxy a).mp he]
        rfl
  diagonal x := by simp
  nonthin := by
    intro x y a ha
    change (if h : x = y then none else (D.edge x y h).map Subtype.val) = some a at ha
    split at ha
    · cases ha
    · rename_i hxy
      cases he : D.edge x y hxy with
      | none => rw [he] at ha; cases ha
      | some b =>
        rw [he] at ha
        cases Option.some.inj ha
        exact b.property.1

theorem pattern_edge {V : Type z} [DecidableEq V] (D : PartialDiagram (source S H R B) V)
    {x y : V} {a : S.Atom () ()} :
    (pattern S H R B D).edge x y = some a ↔
      ∃ hxy : x ≠ y, ∃ b : (source S H R B).Atom (D.vertexSort x) (D.vertexSort y),
        D.edge x y hxy = some b ∧ b.val = a := by
  classical
  by_cases hxy : x = y
  · subst y; simp [pattern]
  · change (if h : x = y then none else (D.edge x y h).map Subtype.val) = some a ↔ _
    rw [dif_neg hxy]
    constructor
    · intro ha
      cases he : D.edge x y hxy with
      | none => rw [he] at ha; cases ha
      | some b =>
        rw [he] at ha
        exact ⟨hxy,b,he,Option.some.inj ha⟩
    · rintro ⟨_,b,hb,he⟩
      rw [hb]
      exact congrArg some he

/-- Actual packet-separated origin completion is a typed strong completion. -/
theorem completion_of_origin_pattern {V : Type z} [DecidableEq V] (D : PartialDiagram (source S H R B) V)
    (f : OriginMap S H R B (pattern S H R B D)) (hsep : f.PacketSeparated) :
    D.HasStrongCompletion := by
  letI := D.finite_type
  obtain ⟨point,hinj,hc⟩ := embed_origin_pattern S H R B (pattern S H R B D)
    D.vertexSort (fun _ => rfl) f hsep
  let g : DiagramHom D := {
    point := point
    preserves_edge := by
      intro x y hxy a ha
      apply (colour_some_iff S H R B _ _ a).mpr
      exact hc x y a.val ((pattern_edge S H R B D).mpr ⟨hxy,a,ha,rfl⟩) }
  refine ⟨g,?_⟩
  intro x y hxy
  exact hinj (congrArg (sigmaEquiv S H R B) hxy)


/-- Realize any actual old finite table whose literal pairs belong to the
specified U owner palettes. No general owner-compatible table is assumed. -/
theorem realize_old_table {V : Type} [Fintype V] [DecidableEq V]
    (sort : V → ↥B) (raw : V → M)
    (hpal : ∀ x y a, col S (raw x) (raw y) = some a →
      ∃ b : Palette S H R B (sort x) (sort y), b.val = a) :
    ∃ point : ∀ x, Carrier S H R B (sort x),
      Function.Injective (fun x => (point x).val) ∧
      ∀ x y a, col S (raw x) (raw y) = some a →
        (TransversalAge.limitTable S H R B).colour (point x).val (point y).val = some a := by
  let P : OriginPattern S H R V := {
    owner x := (sort x).val
    edge x y := col S (raw x) (raw y)
    symmetric x y := col_symm S _ _
    diagonal x := (col_none S _ _).mpr rfl
    nonthin := by
      intro x y a ha
      obtain ⟨b,rfl⟩ := hpal x y a ha
      exact b.property.1 }
  have hcap : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out := by
    intro x y a ha
    obtain ⟨b,rfl⟩ := hpal x y a ha
    exact palette_compatible S H R B b
  let j : V → NamedCarrier S H R B := fun x => ⟨(sort x).val.out,by
    change (Quotient.mk'' (sort x).val.out : Owner S H R) ∈ B
    exact Eq.mpr (congrArg (fun q : Owner S H R => q ∈ B) (Quotient.out_eq (sort x).val)) (sort x).property⟩
  obtain ⟨f,_,hsep⟩ := protected_transversal_completion S H R B P
    (fun x => (sort x).property) hcap ∅ (by simp [RawRecords.CompleteOn])
    raw (fun _ _ _ ha => ha) j (by simp) (by simp) (by simp)
  exact embed_origin_pattern S H R B P sort (fun _ => rfl) f hsep

/-- Actual old triangle legality is sufficient in the typed U source. -/
theorem original_triangle_source {i j k : ↥B}
    {a : (source S H R B).Atom i j} {b : (source S H R B).Atom j k}
    {c : (source S H R B).Atom i k}
    (h : S.Triangle a.val b.val c.val) : (source S H R B).Triangle a b c := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  let sort : Fin 3 → ↥B := ![i,j,k]
  let raw : Fin 3 → M := ![x,y,z]
  have hdiag (p : M) : col S p p = none := (col_none S _ _).mpr rfl
  have hyx : col S y x = some a.val := (col_symm S y x).trans hxy
  have hzy : col S z y = some b.val := (col_symm S z y).trans hyz
  have hzx : col S z x = some c.val := (col_symm S z x).trans hxz
  have hpal : ∀ r s d, col S (raw r) (raw s) = some d →
      ∃ e : Palette S H R B (sort r) (sort s), e.val = d := by
    intro r s d hd
    fin_cases r <;> fin_cases s
    · change col S x x = some d at hd; rw [hdiag] at hd; cases hd
    · exact ⟨a,Option.some.inj (hxy.symm.trans hd)⟩
    · exact ⟨c,Option.some.inj (hxz.symm.trans hd)⟩
    · exact ⟨converse S H R B a,Option.some.inj (hyx.symm.trans hd)⟩
    · change col S y y = some d at hd; rw [hdiag] at hd; cases hd
    · exact ⟨b,Option.some.inj (hyz.symm.trans hd)⟩
    · exact ⟨converse S H R B c,Option.some.inj (hzx.symm.trans hd)⟩
    · exact ⟨converse S H R B b,Option.some.inj (hzy.symm.trans hd)⟩
    · change col S z z = some d at hd; rw [hdiag] at hd; cases hd
  obtain ⟨point,_,hc⟩ := realize_old_table S H R B sort raw hpal
  exact ⟨point 0,point 1,point 2,
    (colour_some_iff S H R B _ _ a).mpr (hc 0 1 a.val hxy),
    (colour_some_iff S H R B _ _ b).mpr (hc 1 2 b.val hyz),
    (colour_some_iff S H R B _ _ c).mpr (hc 0 2 c.val hxz)⟩

theorem source_triangle_iff_original {i j k : ↥B}
    (a : (source S H R B).Atom i j) (b : (source S H R B).Atom j k)
    (c : (source S H R B).Atom i k) :
    (source S H R B).Triangle a b c ↔ S.Triangle a.val b.val c.val :=
  ⟨source_triangle_original S H R B,original_triangle_source S H R B⟩


/-- Every old specified cycle lifts to the SAME typed formal cycle. -/
def typedCycle {V : Type} [Finite V] [DecidableEq V]
    (D : PartialDiagram (source S H R B) V)
    (C : SimpleCycle (pattern S H R B D).records.diagram) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified p := by
    obtain ⟨a,ha⟩ := C.specified p
    obtain ⟨_,b,hb,_⟩ := (pattern_edge S H R B D).mp ha
    exact ⟨b,hb⟩

theorem pattern_cycle_hom {V : Type} [Finite V] [DecidableEq V]
    (D : PartialDiagram (source S H R B) V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (C : SimpleCycle (pattern S H R B D).records.diagram) : CycleHom C := by
  let T := typedCycle S H R B D C
  obtain ⟨point,hpoint⟩ := hcycles T
  obtain ⟨f,_,hc,_⟩ := TransversalAge.realize_tuple S H R B (fun p => (point p).val)
  refine ⟨fun p => (f p).val,?_⟩
  intro p a ha
  obtain ⟨_,b,hb,he⟩ := (pattern_edge S H R B D).mp ha
  have htyped := hpoint p b hb
  exact (hc p (cyclicNext C.length_pos p)).trans
    (((colour_some_iff S H R B _ _ b).mp htyped).trans (congrArg some he))

/-- Semantic CCO is discharged for the ACTUAL U-owner source. Every
specified typed cycle is checked before protected transversal completion. -/
theorem semanticCCO : SemanticCCO.{v,0,0,w} (source S H R B) := by
  classical
  intro V D hcycles
  letI := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let P := pattern S H R B D
  have hcap : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out := by
    intro x y a ha
    obtain ⟨_,b,_,rfl⟩ := (pattern_edge S H R B D).mp ha
    exact palette_compatible S H R B b
  let j : V → NamedCarrier S H R B := fun x => ⟨(D.vertexSort x).val.out,by
    change (Quotient.mk'' (D.vertexSort x).val.out : Owner S H R) ∈ B
    exact Eq.mpr (congrArg (fun q : Owner S H R => q ∈ B)
      (Quotient.out_eq (D.vertexSort x).val)) (D.vertexSort x).property⟩
  obtain ⟨f,_,hsep⟩ := protected_transversal_CCO S H R B P
    (fun x => (D.vertexSort x).property) hcap (pattern_cycle_hom S H R B D hcycles)
    ∅ (by simp [RawRecords.CompleteOn]) j (by simp) (by simp) (by simp)
  obtain ⟨g,_⟩ := completion_of_origin_pattern S H R B D f hsep
  exact ⟨g⟩

end
end CCO.SafeReadings.TransversalSource
