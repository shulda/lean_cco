import CCO.OrbitalCover.Example.Prefixes

universe z
namespace CCO.OrbitalCover.Example.Prefix

def pLabel (k : Stage) (c : child k) : Bit :=
  match k with
  | .first => c.2
  | .both => c.2.1
def qLabel (c : child .both) : Bit := c.2.2

theorem point_p (k : Stage) {c : child k} (x : carrier k c) : x.val.p = pLabel k c := by
  cases k with
  | first => exact x.property
  | both => exact congrArg Prod.fst x.property
theorem point_q {c : child .both} (x : carrier .both c) : x.val.q = qLabel c :=
  congrArg Prod.snd x.property

def oldDiagram (k : Stage) {V : Type z} (D : PartialDiagram (source k) V) :
    PartialDiagram Example.source V where
  finite_type := D.finite_type
  vertexSort _ := ()
  edge x y h := (D.edge x y h).map Subtype.val
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      rfl
    · intro ha
      obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse y x h.symm b).mp hb]
      change some b.val = some a
      exact congrArg some he

def newCycle (k : Stage) {V : Type z} (D : PartialDiagram (source k) V)
    (C : SimpleCycle (oldDiagram k D)) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified := by
    intro p
    obtain ⟨a,ha⟩ := C.specified p
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨b,hb⟩

theorem old_cycle_hom (k : Stage) {V : Type z} (D : PartialDiagram (source k) V)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) (C : SimpleCycle (oldDiagram k D)) :
    CycleHom C := by
  obtain ⟨p,hp⟩ := cycles (newCycle k D C)
  refine ⟨fun i => (p i).val,?_⟩
  intro i a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  have hh := congrArg (Option.map Subtype.val) (hp i b hb)
  exact (colour_map k (p i) (p (cyclicNext C.length_pos i))).symm.trans hh

theorem atom_p (k : Stage) {c d : child k} (a : (source k).Atom c d)
    (b : Bit) (ha : a.val.1 = some b) : pLabel k c + pLabel k d = b := by
  obtain ⟨x,y,hxy⟩ := a.property
  have hcol := ((Example.colour_some x.val y.val a.val).mp hxy).2
  have hcoord : coordinateColour x.val.u x.val.p y.val.u y.val.p = some b :=
    (congrArg Prod.fst hcol).trans ha
  simpa only [point_p] using (coordinateColour_some _ _ _ _ _).mp hcoord |>.2

theorem atom_q {c d : child .both} (a : (source .both).Atom c d)
    (b : Bit) (ha : a.val.2 = some b) : qLabel c + qLabel d = b := by
  obtain ⟨x,y,hxy⟩ := a.property
  have hcol := ((Example.colour_some x.val y.val a.val).mp hxy).2
  have hcoord : coordinateColour x.val.v x.val.q y.val.v y.val.q = some b :=
    (congrArg Prod.snd hcol).trans ha
  simpa only [point_q] using (coordinateColour_some _ _ _ _ _).mp hcoord |>.2

def qPrescription (k : Stage) {V : Type z} (D : PartialDiagram (source k) V) :
    Option (V → Bit) := match k with
  | .first => none
  | .both => some (fun x => qLabel (D.vertexSort x))

/-- Actual direct CCO with the chosen literal named predicates retained.
Every local signed requirement is read from an actual occurring child atom. -/
theorem semanticCCO (k : Stage) : SemanticCCO.{0,0,z,0} (source k) := by
  intro V D cycles
  let P : V → Bit := fun x => pLabel k (D.vertexSort x)
  have hP : ∀ p, some P = some p → ∀ x y (h : x ≠ y)
      (a : Example.source.Atom ((oldDiagram k D).vertexSort x) ((oldDiagram k D).vertexSort y))
      (b : Bit), (oldDiagram k D).edge x y h = some a → a.1 = some b → p x + p y = b := by
    intro p hp x y h a b ha hb
    have he : P = p := Option.some.inj hp
    subst p
    obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp ha
    exact atom_p k c b hb
  have hQ : ∀ q, qPrescription k D = some q → ∀ x y (h : x ≠ y)
      (a : Example.source.Atom ((oldDiagram k D).vertexSort x) ((oldDiagram k D).vertexSort y))
      (b : Bit), (oldDiagram k D).edge x y h = some a → a.2 = some b → q x + q y = b := by
    cases k with
    | first => intro q hq; cases hq
    | both =>
      intro q hq x y h a b ha hb
      have he : (fun x => qLabel (D.vertexSort x)) = q := Option.some.inj hq
      subst q
      obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp ha
      exact atom_q c b hb
  obtain ⟨f,hfi,hfp,hfq⟩ := realize_prescribed V (oldDiagram k D)
    (old_cycle_hom k D cycles) (some P) (qPrescription k D) hP hQ
  have hm (x : V) : mark k (f.point x) = (D.vertexSort x).2 := by
    cases k with
    | first => exact hfp P rfl x
    | both =>
      exact Prod.ext (hfp P rfl x) (hfq (fun x => qLabel (D.vertexSort x)) rfl x)
  refine ⟨{
    point := fun x => ⟨f.point x,hm x⟩
    preserves_edge := ?_
  }⟩
  intro x y h a ha
  apply (colour_some k _ _ a).mpr
  apply f.preserves_edge x y h a.val
  change (D.edge x y h).map Subtype.val = some a.val
  rw [ha]
  rfl

theorem triangle_defined (k : Stage) {V : Type z} (A : CompleteDiagram (S := source k) V)
    (hsmall : A.SmallRealizable) : ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_homogeneous_CCO (homogeneous k) (semanticCCO k) hsmall

end CCO.OrbitalCover.Example.Prefix
