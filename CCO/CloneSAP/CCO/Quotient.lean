import CCO.CloneSAP.CCO.Parallel

/-! The actual diversity-only c-component quotient. All edge labels are
literal old atoms, deduplicated using the proved parallel-cycle obstruction. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)

abbrev Component := (cloneGraph S D).ConnectedComponent
abbrev component (x : V) : Component S D := (cloneGraph S D).connectedComponentMk x

/-- A genuine old edge, including its exact original endpoints and orientation. -/
def OldBetween (A B : Component S D)
    (a : S.Atom (componentSort S D A) (componentSort S D B)) : Prop :=
  ∃ (x y : V) (h : x ≠ y) (b : S.Atom (D.vertexSort x) (D.vertexSort y)),
    component S D x = A ∧ component S D y = B ∧ D.edge x y h = some (.inl b) ∧
    (⟨D.vertexSort x,D.vertexSort y,some b⟩ : Σ i, Σ j, Option (S.Atom i j)) =
      ⟨componentSort S D A,componentSort S D B,some a⟩

def reverseTag (t : Σ i, Σ j, Option (S.Atom i j)) : Σ i, Σ j, Option (S.Atom i j) :=
  ⟨t.2.1,t.1,t.2.2.map S.conv⟩

theorem OldBetween.reverse {A B : Component S D}
    {a : S.Atom (componentSort S D A) (componentSort S D B)}
    (h : OldBetween S D A B a) : OldBetween S D B A (S.conv a) := by
  obtain ⟨x,y,hne,b,hx,hy,he,htag⟩ := h
  refine ⟨y,x,hne.symm,S.conv b,hy,hx,(D.edge_reverse x y hne (.inl b)).mp he,?_⟩
  exact congrArg (reverseTag S) htag

theorem OldBetween.unique
    (cycles : ∀ C : SimpleCycle D, CycleHom C) {A B : Component S D}
    {a b : S.Atom (componentSort S D A) (componentSort S D B)}
    (ha : OldBetween S D A B a) (hb : OldBetween S D A B b) : a = b := by
  obtain ⟨x,y,hne,c,hx,hy,he,htag⟩ := ha
  obtain ⟨x',y',hne',c',hx',hy',he',htag'⟩ := hb
  have ht := old_parallel_labels S D cycles x y x' y' hne hne' c c' he he'
    (hx.trans hx'.symm) (hy.trans hy'.symm)
  have hh := htag.symm.trans (ht.trans htag')
  exact Option.some.inj (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2)

noncomputable def quotientEdge (A B : Component S D) :
    Option (S.Atom (componentSort S D A) (componentSort S D B)) := by
  classical
  exact if h : ∃ a, OldBetween S D A B a then some (Classical.choose h) else none

theorem quotientEdge_iff (cycles : ∀ C : SimpleCycle D, CycleHom C)
    {A B : Component S D} (a : S.Atom (componentSort S D A) (componentSort S D B)) :
    quotientEdge S D A B = some a ↔ OldBetween S D A B a := by
  classical
  unfold quotientEdge
  split_ifs with h
  · constructor
    · intro ha
      have he : Classical.choose h = a := Option.some.inj ha
      exact he ▸ Classical.choose_spec h
    · intro ha
      exact congrArg some (OldBetween.unique S D cycles (Classical.choose_spec h) ha)
  · constructor
    · simp
    · intro ha
      exact (h ⟨a,ha⟩).elim

/-- D06/C17: a finite typed OLD diversity partial graph. No equality edge
is inserted; unused components, including isolated vertices, remain. -/
noncomputable def quotientDiagram (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    PartialDiagram S (Component S D) where
  finite_type := by
    letI : Finite V := D.finite_type
    infer_instance
  vertexSort := componentSort S D
  edge A B _ := quotientEdge S D A B
  edge_reverse A B _ a := by
    simp only [quotientEdge_iff S D cycles]
    constructor
    · exact OldBetween.reverse S D
    · intro h
      have hh := OldBetween.reverse S D h
      simpa only [S.conv_invol] using hh

theorem quotient_specified (cycles : ∀ C : SimpleCycle D, CycleHom C)
    {A B : Component S D} {h : A ≠ B}
    {a : S.Atom (componentSort S D A) (componentSort S D B)}
    (ha : (quotientDiagram S D cycles).edge A B h = some a) :
    OldBetween S D A B a := (quotientEdge_iff S D cycles a).mp ha

theorem quotient_old_edge (cycles : ∀ C : SimpleCycle D, CycleHom C)
    (x y : V) (h : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y h = some (.inl a)) :
    (quotientDiagram S D cycles).edge (component S D x) (component S D y)
      (old_edge_distinct_components S D cycles x y h a ha) = some a := by
  apply (quotientEdge_iff S D cycles
    (A := component S D x) (B := component S D y) a).mpr
  exact ⟨x,y,h,a,rfl,rfl,ha,rfl⟩

end CCO.CloneSAP.CCO
