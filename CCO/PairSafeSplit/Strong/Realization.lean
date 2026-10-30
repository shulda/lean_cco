import CCO.APCharacter.SourceAge.UnarySourceHomogeneity
import CCO.APCharacter.MarkedSource

/-! B047 C34–C35: actual finite legal tuples in the whole marked limit.
Repeated old points are retained. All source instances below use the proved
finite seed theorem and genuine Fraisse age; no SAP or homogeneous-seed
premise is introduced. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong.Realization
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
open OwnerTransversal.CountableColour
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {a : ι} {A : Kernel S a}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)

theorem global_marking_of_legal_tuple {V : Type} [Finite V]
    (point : V → Sigma X) (bits : V → Bit) (legal : Age.Legal S P.masks point bits) :
    ∃ mark : Sigma X → Bit, P.masks.GlobalMarking mark ∧
      ∀ x, mark (point x) = bits x := by
  obtain ⟨mark,hm,he⟩ := P.finite_seed_extension
    (fun x : ULift.{max u v} V => (point x.down).1)
    (fun x => (point x.down).2) (fun x => bits x.down)
    (fun x => legal.1 x.down) (fun x y => legal.2 x.down y.down)
  exact ⟨mark,hm,fun x => he (ULift.up x)⟩

theorem embed_legal_tuple_limit {V : Type} [Finite V]
    (point : V → Sigma X) (bits : V → Bit) (legal : Age.Legal S P.masks point bits) :
    ∃ f : V → P.MarkedLimit cco,
      (∀ x, (Age.limitCoding S H (P.completion_property cco)).table.owner (f x) =
        Age.ownerEquiv S ((point x).1,bits x)) ∧
      ∀ x y, (Age.limitCoding S H (P.completion_property cco)).table.colour (f x) (f y) =
        Age.colourEquiv S (taggedColour S (point x) (point y)) := by
  classical
  obtain ⟨mark,hm,hmark⟩ := global_marking_of_legal_tuple P point bits legal
  let D : PartialDiagram S V := {
    finite_type := inferInstance
    vertexSort x := (point x).1
    edge _ _ _ := none
    edge_reverse := by intro x y h a; simp }
  let F : DiagramHom D := {
    point x := (point x).2
    preserves_edge := by intro x y h a ha; cases ha }
  let T := Age.FiniteImage.table F mark
  have hT : Age.Realized S P.masks T := Age.FiniteImage.realized F mark hm
  let chart := Age.chartOf S T hT
  letI := T.toStructure
  letI := chart.structure
  let iso := Age.chartOfEquiv S T hT
  have hn := T.embedding_preserves chart.table iso.toEmbedding
  obtain ⟨e,ho,hc⟩ := Age.chart_names S H (P.completion_property cco) chart
  let f : V → P.MarkedLimit cco := fun x => e (iso (Quotient.mk _ x))
  refine ⟨f,?_,?_⟩
  · intro x
    have hx := (ho (iso (Quotient.mk _ x))).trans (hn.1 (Quotient.mk _ x))
    change (Age.limitCoding S H (P.completion_property cco)).table.owner (f x) = _ at hx ⊢
    apply hx.trans
    change Age.ownerEquiv S ((point x).1,mark (point x)) = _
    rw [hmark]
  · intro x y
    have hxy := (hc (iso (Quotient.mk _ x)) (iso (Quotient.mk _ y))).trans
      (hn.2 (Quotient.mk _ x) (Quotient.mk _ y))
    change (Age.limitCoding S H (P.completion_property cco)).table.colour (f x) (f y) = _ at hxy ⊢
    exact hxy

variable (I : Identification S H (P.completion_property cco))

/-- The actual canonical child-source version, with literal endpoint
sort/bit names and every old optional pair colour preserved. -/
theorem embed_legal_tuple {V : Type} [Finite V]
    (point : V → Sigma X) (bits : V → Bit) (legal : Age.Legal S P.masks point bits) :
    ∃ f : V → NewPoint I,
      (∀ x, childLabel I (f x).1 = ((point x).1,bits x)) ∧
      ∀ x y, taggedColour S (oldEquiv I (f x)) (oldEquiv I (f y)) =
        taggedColour S (point x) (point y) := by
  obtain ⟨e,ho,hc⟩ := embed_legal_tuple_limit P cco point bits legal
  let f : V → NewPoint I := (newEquiv I).symm ∘ e
  have he (x : V) : newEquiv I (f x) = e x := (newEquiv I).apply_symm_apply _
  refine ⟨f,?_,?_⟩
  · intro x
    apply (Age.ownerEquiv S).injective
    exact (new_owner I (f x)).symm.trans ((congrArg
      (Age.limitCoding S H (P.completion_property cco)).table.owner (he x)).trans (ho x))
  · intro x y
    apply (Age.colourEquiv S).injective
    rw [← erase_tagged I,← new_colour I,he,he]
    exact hc x y

/-- Name preservation reflects the whole old equality pattern. -/
theorem injective_of_old_names {V : Type} (point : V → Sigma X) (f : V → NewPoint I)
    (hc : ∀ x y, taggedColour S (oldEquiv I (f x)) (oldEquiv I (f y)) =
      taggedColour S (point x) (point y)) (hp : Function.Injective point) :
    Function.Injective f := by
  intro x y he
  apply hp
  apply (equality_iff S _ _ _ _ (hc x y)).mp
  exact congrArg (oldEquiv I) he

/-- A finite legal tuple can be placed over any already named tuple of
the same full old/bit type. The base may have repetitions; homogeneity is
that of the entire actual limit, never of a chosen seed marking. -/
theorem align_legal_tuple {V W : Type} [Finite V] [Finite W]
    (point : W → Sigma X) (bits : W → Bit) (legal : Age.Legal S P.masks point bits)
    (j : V → W) (p : V → NewPoint I)
    (hpOwner : ∀ x, childLabel I (p x).1 = ((point (j x)).1,bits (j x)))
    (hpColour : ∀ x y, taggedColour S (oldEquiv I (p x)) (oldEquiv I (p y)) =
      taggedColour S (point (j x)) (point (j y))) :
    ∃ r : W → NewPoint I,
      (∀ x, childLabel I (r x).1 = ((point x).1,bits x)) ∧
      (∀ x y, taggedColour S (oldEquiv I (r x)) (oldEquiv I (r y)) =
        taggedColour S (point x) (point y)) ∧
      ∀ x, r (j x) = p x := by
  obtain ⟨f,hOwner,hColour⟩ := embed_legal_tuple P cco I point bits legal
  let left : V → P.MarkedLimit cco := fun x => newEquiv I (f (j x))
  let right : V → P.MarkedLimit cco := fun x => newEquiv I (p x)
  have hEq : ∀ x y, left x = left y ↔ right x = right y := by
    intro x y
    change newEquiv I (f (j x)) = newEquiv I (f (j y)) ↔
      newEquiv I (p x) = newEquiv I (p y)
    rw [(newEquiv I).injective.eq_iff,(newEquiv I).injective.eq_iff]
    have he := equality_iff S _ _ _ _ ((hColour (j x) (j y)).trans (hpColour x y).symm)
    simpa only [(oldEquiv I).injective.eq_iff] using he
  have hOwnerEq : ∀ x,
      (Age.limitCoding S H (P.completion_property cco)).table.owner (left x) =
        (Age.limitCoding S H (P.completion_property cco)).table.owner (right x) := by
    intro x
    rw [new_owner,new_owner,hOwner,hpOwner]
  have hColourEq : ∀ x y,
      (Age.limitCoding S H (P.completion_property cco)).table.colour (left x) (left y) =
        (Age.limitCoding S H (P.completion_property cco)).table.colour (right x) (right y) := by
    intro x y
    change (Age.limitCoding S H (P.completion_property cco)).table.colour
      (newEquiv I (f (j x))) (newEquiv I (f (j y))) =
      (Age.limitCoding S H (P.completion_property cco)).table.colour
        (newEquiv I (p x)) (newEquiv I (p y))
    rw [new_colour,new_colour,erase_tagged,erase_tagged,hColour,hpColour]
  obtain ⟨g,hg⟩ := Age.tuple_homogeneous S H (P.completion_property cco)
    left right hEq hOwnerEq hColourEq
  let g' : FullGroup I := ULift.up g
  let r : W → NewPoint I := fun x => g' • f x
  refine ⟨r,?_,?_,?_⟩
  · intro x
    have hs : (r x).1 = (f x).1 := (homogeneous I).preserves_sort g' (f x)
    rw [hs,hOwner]
  · intro x y
    have hc := action_colours I g' (f x) (f y)
    have old := congrArg (eraseColour I) hc
    rw [erase_tagged,erase_tagged] at old
    exact old.trans (hColour x y)
  · intro x
    apply (newEquiv I).injective
    exact (smul_image I g' (f (j x))).trans (hg x)

/-- The fixed-base finite induced embedding version used for actual marked
SAP. Injectivity is deduced from the supplied ACTUAL old induced tuple. -/
theorem extend_legal_embedding {V W : Type} [Finite V] [Finite W]
    (point : W ↪ Sigma X) (bits : W → Bit) (legal : Age.Legal S P.masks point bits)
    (j : V ↪ W) (p : V ↪ NewPoint I)
    (hpOwner : ∀ x, childLabel I (p x).1 = ((point (j x)).1,bits (j x)))
    (hpColour : ∀ x y, taggedColour S (oldEquiv I (p x)) (oldEquiv I (p y)) =
      taggedColour S (point (j x)) (point (j y))) :
    ∃ r : W ↪ NewPoint I,
      (∀ x, childLabel I (r x).1 = ((point x).1,bits x)) ∧
      (∀ x y, taggedColour S (oldEquiv I (r x)) (oldEquiv I (r y)) =
        taggedColour S (point x) (point y)) ∧
      ∀ x, r (j x) = p x := by
  obtain ⟨r,ho,hc,he⟩ := align_legal_tuple P cco I point bits legal j p hpOwner hpColour
  exact ⟨⟨r,injective_of_old_names P cco I point r hc point.injective⟩,ho,hc,he⟩

end
end CCO.PairSafeSplit.Strong.Realization
