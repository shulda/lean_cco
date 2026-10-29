import CCO.SafeReadings.TransversalSource

/-! Actual strong amalgamation of the typed owner-fibre source.  Every finite
typed induced structure is represented by an ACTUAL finite origin chart;
the accepted chart SAP is then realized in the same internally constructed U.
No original real-age SAP or additional transversal-source provider is assumed. -/
open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.SafeReadings.TransversalSource
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds OwnerTransversal
open CountableColour

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

abbrev TypedFinite := FiniteInduced (X := Carrier S H R B)

/-- Reindexing retains literal owners and every ordered fine-colour entry. -/
structure FiniteChart (A : TypedFinite S H R B) where
  chart : TransversalAge.Chart S H R B
  index : ↥A.vertices ≃ Fin chart.n
  owner : ∀ a, chart.table.owner (index a) = a.val.1
  colour : ∀ a b, chart.table.colour (index a) (index b) =
    (TransversalAge.limitTable S H R B).colour a.val.2.val b.val.2.val

/-- The actual finite U tuple is read in one original separated-origin chart. -/
def finiteChart (A : TypedFinite S H R B) : FiniteChart S H R B A := by
  letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
  letI : Fintype ↥A.vertices := Fintype.ofFinite _
  let k := Fintype.equivFin ↥A.vertices
  let u : Fin (Fintype.card ↥A.vertices) → TransversalAge.U S H R B :=
    fun i => (sigmaEquiv S H R B) (k.symm i).val
  have hu : Function.Injective u := by
    intro i j hij
    apply k.symm.injective
    apply Subtype.ext
    exact (sigmaEquiv S H R B).injective hij
  let h := TransversalAge.realize_tuple S H R B u
  let f := h.choose
  have hfo := h.choose_spec.1
  have hfc := h.choose_spec.2.1
  have hsep := h.choose_spec.2.2
  let Q : TransversalAge.Chart S H R B := {
    n := Fintype.card ↥A.vertices
    table := ⟨fun i => (TransversalAge.limitTable S H R B).owner (u i),
      fun i j => (TransversalAge.limitTable S H R B).colour (u i) (u j)⟩
    realized := ⟨⟨f,hfo,hfc,fun i j hij => hsep i j (fun he => hij (hu he))⟩⟩ }
  refine ⟨Q,k,?_,?_⟩
  · intro a
    change (TransversalAge.limitTable S H R B).owner ((k.symm (k a)).val.2.val) = a.val.1
    rw [Equiv.symm_apply_apply]
    exact a.val.2.property
  · intro a b
    change (TransversalAge.limitTable S H R B).colour ((k.symm (k a)).val.2.val)
      ((k.symm (k b)).val.2.val) = _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

namespace FiniteChart
variable {S H R B}

/-- Any actual typed induced embedding becomes a genuine embedding of the
whole literal owner/colour language on its two finite charts. -/
def map {C A : TypedFinite S H R B} (c : FiniteChart S H R B C)
    (a : FiniteChart S H R B A) (e : InducedEmbedding (source S H R B) C A) :
    Fin c.chart.n ↪[TransversalAge.Signature S H R B] Fin a.chart.n := by
  let f : Fin c.chart.n ↪ Fin a.chart.n := {
    toFun z := a.index (e.toEmbedding (c.index.symm z))
    inj' := a.index.injective.comp (e.toEmbedding.injective.comp c.index.symm.injective) }
  apply Table.embedding c.chart.table a.chart.table f
  · intro i
    exact (a.owner _).trans ((e.preserves_sort _).trans
      (c.owner (c.index.symm i)).symm) |>.trans
        (congrArg c.chart.table.owner (c.index.apply_symm_apply i))
  · intro i j
    have hc := congrArg (forgetColour S H R B)
      (e.preserves_colours (c.index.symm i) (c.index.symm j))
    simp only [forget_tagged] at hc
    exact (a.colour _ _).trans (hc.symm.trans
      ((c.colour (c.index.symm i) (c.index.symm j)).symm.trans (by
        rw [c.index.apply_symm_apply,c.index.apply_symm_apply])))

@[simp] theorem map_index {C A : TypedFinite S H R B} (c : FiniteChart S H R B C)
    (a : FiniteChart S H R B A) (e : InducedEmbedding (source S H R B) C A)
    (x : ↥C.vertices) : c.map a e (c.index x) = a.index (e.toEmbedding x) := by
  change a.index (e.toEmbedding (c.index.symm (c.index x))) = _
  rw [Equiv.symm_apply_apply]

end FiniteChart

/-- C40: SAP holds for arbitrary finite typed induced spans in the actual
U owner fibres, with exactly the designated common base. -/
theorem ageSAP : AgeSAP (source S H R B) := by
  classical
  refine ⟨?_⟩
  intro C A P eCA eCP
  letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
  letI : Finite ↥P.vertices := P.finite_vertices.to_subtype
  let c := finiteChart S H R B C
  let a := finiteChart S H R B A
  let p := finiteChart S H R B P
  obtain ⟨Q,i,j,hcomm,hcross⟩ := TransversalAge.Chart.strong_amalgamation
    c.chart a.chart p.chart (c.map a eCA) (c.map p eCP)
  obtain ⟨u,huo,huc⟩ := TransversalAge.embed_chart S H R B Q
  have hi := Table.embedding_preserves a.chart.table Q.table i
  have hj := Table.embedding_preserves p.chart.table Q.table j
  let l : ↥A.vertices ↪ (Σ b : ↥B, Carrier S H R B b) := {
    toFun x := (sigmaEquiv S H R B).symm (u (i (a.index x)))
    inj' := (sigmaEquiv S H R B).symm.injective.comp
      (u.injective.comp (i.injective.comp a.index.injective)) }
  let r : ↥P.vertices ↪ (Σ b : ↥B, Carrier S H R B b) := {
    toFun x := (sigmaEquiv S H R B).symm (u (j (p.index x)))
    inj' := (sigmaEquiv S H R B).symm.injective.comp
      (u.injective.comp (j.injective.comp p.index.injective)) }
  have hlSort (x : ↥A.vertices) : (l x).1 = x.val.1 := by
    change (TransversalAge.limitTable S H R B).owner (u (i (a.index x))) = _
    rw [huo,hi.1,a.owner]
  have hrSort (x : ↥P.vertices) : (r x).1 = x.val.1 := by
    change (TransversalAge.limitTable S H R B).owner (u (j (p.index x))) = _
    rw [huo,hj.1,p.owner]
  have hlColour (x y : ↥A.vertices) :
      taggedColour (source S H R B) x.val y.val =
        taggedColour (source S H R B) (l x) (l y) := by
    apply tagged_eq S H R B (hlSort x).symm (hlSort y).symm
    change _ = (TransversalAge.limitTable S H R B).colour (u (i (a.index x))) (u (i (a.index y)))
    rw [huc,hi.2,a.colour]
  have hrColour (x y : ↥P.vertices) :
      taggedColour (source S H R B) x.val y.val =
        taggedColour (source S H R B) (r x) (r y) := by
    apply tagged_eq S H R B (hrSort x).symm (hrSort y).symm
    change _ = (TransversalAge.limitTable S H R B).colour (u (j (p.index x))) (u (j (p.index y)))
    rw [huc,hj.2,p.colour]
  let D : TypedFinite S H R B := {
    vertices := Set.range l ∪ Set.range r
    finite_vertices := (Set.finite_range l).union (Set.finite_range r) }
  let eAD : InducedEmbedding (source S H R B) A D := {
    toEmbedding := {
      toFun x := ⟨l x,Or.inl ⟨x,rfl⟩⟩
      inj' := fun x y h => l.injective (congrArg Subtype.val h) }
    preserves_sort := hlSort
    preserves_colours := hlColour }
  let ePD : InducedEmbedding (source S H R B) P D := {
    toEmbedding := {
      toFun x := ⟨r x,Or.inr ⟨x,rfl⟩⟩
      inj' := fun x y h => r.injective (congrArg Subtype.val h) }
    preserves_sort := hrSort
    preserves_colours := hrColour }
  refine ⟨D,eAD,ePD,?_,?_⟩
  · intro x
    have he := DFunLike.congr_fun hcomm (c.index x)
    change i (c.map a eCA (c.index x)) = j (c.map p eCP (c.index x)) at he
    rw [FiniteChart.map_index,FiniteChart.map_index] at he
    apply Subtype.ext
    exact congrArg (fun z => (sigmaEquiv S H R B).symm (u z)) he
  · intro x y hxy
    have hσ := congrArg (fun z : ↥D.vertices => (sigmaEquiv S H R B) z.val) hxy
    have huv : u (i (a.index x)) = u (j (p.index y)) := by
      change (sigmaEquiv S H R B) ((sigmaEquiv S H R B).symm (u (i (a.index x)))) =
        (sigmaEquiv S H R B) ((sigmaEquiv S H R B).symm (u (j (p.index y)))) at hσ
      simpa only [Equiv.apply_symm_apply] using hσ
    obtain ⟨z,hzx,hzy⟩ := (hcross (a.index x) (p.index y)).mp (u.injective huv)
    refine ⟨c.index.symm z,?_,?_⟩
    · apply a.index.injective
      change a.index (eCA.toEmbedding (c.index.symm z)) = a.index x
      exact hzx
    · apply p.index.injective
      change p.index (eCP.toEmbedding (c.index.symm z)) = p.index y
      exact hzy

end
end CCO.SafeReadings.TransversalSource
