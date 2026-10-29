import CCO.OwnerTransversal.AnchoredCompletion

/-! Exact owner caps.  Equality is handled by a genuine identified
formal diagram; a joint family of diversity records is checked on the
simple cycles of the WHOLE augmented diagram. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

noncomputable def RawRecords.diagram {V : Type} [Finite V] (D : RawRecords S V) :
    PartialDiagram S V where
  finite_type := inferInstance
  vertexSort := fun _ => ()
  edge := fun x y _ => D.edge x y
  edge_reverse := by
    intro x y h a
    rw [S.symmetricLoop,D.symmetric]

theorem RawRecords.diagramHom_iff {V : Type} [Finite V] (D : RawRecords S V) :
    Nonempty (DiagramHom (RawRecords.diagram S D)) ↔ ∃ f : V → M, RawRecords.Hom S D f := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.point,?_⟩
    intro x y a ha
    have hne : x ≠ y := by intro hh; subst y; rw [D.diagonal] at ha; cases ha
    exact f.preserves_edge x y hne a ha
  · rintro ⟨f,hf⟩
    exact ⟨⟨f,fun x y _ a ha => hf x y a ha⟩⟩

theorem saturate_transport (E : Setoid M) (R : Relation M) {x y x' y' : M}
    (hx : E x' x) (hy : E y y') (h : ownerSaturate E R x y) :
    ownerSaturate E R x' y' := by
  obtain ⟨z,⟨u,hxu,huz⟩,hzy⟩ := h
  exact ⟨z,⟨u,E.trans hx hxu,huz⟩,E.trans hzy hy⟩

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
/-- C12. This is quantified over the COMPLETE augmented record set:
independent one-edge cap tests are not substituted for its cycle tests. -/
theorem joint_owner_caps {V : Type} [Finite V] (D : RawRecords S V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (owner : V → M) :
    (∃ f : V → M, RawRecords.Hom S D f ∧ ∀ x, E (owner x) (f x)) ↔
      (∀ C : SimpleCycle (RawRecords.diagram S D), CycleHom C) ∧
      (∀ x y a, D.edge x y = some a →
        ownerSaturate E.val (S.atomRel a) (owner x) (owner y)) := by
  constructor
  · rintro ⟨f,hf,hOwn⟩
    refine ⟨?_,?_⟩
    · intro C
      exact ⟨fun k => f (C.vertices k),fun k a ha => hf _ _ a ha⟩
    · intro x y a ha
      exact ⟨f y,⟨f x,hOwn x,hf x y a ha⟩,E.val.symm (hOwn y)⟩
  · rintro ⟨hCycles,hOwner⟩
    obtain ⟨raw,hraw⟩ := (RawRecords.diagramHom_iff S D).mp (cco V (RawRecords.diagram S D) hCycles)
    obtain ⟨f,hf,hOwn,_⟩ := anchored_completion_of_aligned S H D cco E hne word hword
      ∅ (by simp [RawRecords.CompleteOn]) owner raw hraw hOwner (by simp)
    exact ⟨f,hf,hOwn⟩

include H in
/-- C11's general identification lemma. A raw hom and the prescribed
owners descend through the SAME actual formal equivalence. No diversity
loop, conflicting edge or extra completion provider is assumed. -/
theorem identified_owner_completion {V : Type} [Finite V] (D : RawRecords S V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (owner raw : V → M) (hraw : RawRecords.Hom S D raw)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (K : Setoid V) (hRawDesc : ∀ x y, K x y → raw x = raw y)
    (hOwnerDesc : ∀ x y, K x y → E (owner x) (owner y)) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧
      ∀ x y, K x y → f x = f y := by
  classical
  let rawQ : Quotient K → M := Quotient.lift raw hRawDesc
  let ownerClass : Quotient K → Quotient E.val :=
    Quotient.lift (fun x => (Quotient.mk'' (owner x) : Quotient E.val))
      (fun x y h => Quotient.sound (hOwnerDesc x y h))
  let ownerQ : Quotient K → M := fun q => (ownerClass q).out
  have hOwn (x : V) : E (owner x) (ownerQ (Quotient.mk'' x)) :=
    E.val.symm (Quotient.exact (Quotient.out_eq (Quotient.mk'' (owner x))))
  let recorded (q r : Quotient K) : Prop := ∃ x y a,
    (Quotient.mk'' x : Quotient K) = q ∧ Quotient.mk'' y = r ∧ D.edge x y = some a
  have hRecorded (q r : Quotient K) : recorded q r ↔ recorded r q := by
    constructor <;> rintro ⟨x,y,a,hx,hy,ha⟩
    · exact ⟨y,x,a,hy,hx,(D.symmetric y x).trans ha⟩
    · exact ⟨y,x,a,hy,hx,(D.symmetric y x).trans ha⟩
  let Q : RawRecords S (Quotient K) := {
    edge := fun q r => if recorded q r then S.colour (i := ()) (j := ()) (rawQ q) (rawQ r) else none
    diagonal := fun q => by
      rw [(S.colour_none_iff _ _).mpr rfl]
      split_ifs <;> rfl
    symmetric := fun q r => by rw [hRecorded q r,colour_symmetric S] }
  have hQRaw : RawRecords.Hom S Q rawQ := by
    intro q r a ha
    dsimp only [Q] at ha
    split_ifs at ha
    exact ha
  have hQOwn : ∀ q r a, Q.edge q r = some a →
      ownerSaturate E.val (S.atomRel a) (ownerQ q) (ownerQ r) := by
    intro q r a ha
    dsimp only [Q] at ha
    split_ifs at ha with hRec
    obtain ⟨x,y,b,hx,hy,hxy⟩ := hRec
    subst q
    subst r
    have hcol := hraw x y b hxy
    have hab : a = b := Option.some.inj (ha.symm.trans hcol)
    subst a
    exact saturate_transport E.val (S.atomRel b) (E.val.symm (hOwn x)) (hOwn y)
      (hOwner x y b hxy)
  obtain ⟨g,hg,hgOwn,_⟩ := anchored_completion_of_aligned S H Q cco E hne word hword
    ∅ (by simp [RawRecords.CompleteOn]) ownerQ rawQ hQRaw hQOwn (by simp)
  refine ⟨fun x => g (Quotient.mk'' x),?_,?_,?_⟩
  · intro x y a ha
    apply hg (Quotient.mk'' x) (Quotient.mk'' y) a
    have hRec : recorded (Quotient.mk'' x) (Quotient.mk'' y) := ⟨x,y,a,rfl,rfl,ha⟩
    change (if recorded (Quotient.mk'' x) (Quotient.mk'' y) then
      S.colour (i := ()) (j := ()) (raw x) (raw y) else none) = some a
    rw [if_pos hRec]
    exact hraw x y a ha
  · intro x
    exact E.val.trans (hOwn x) (hgOwn (Quotient.mk'' x))
  · intro x y hxy
    exact congrArg g (Quotient.sound hxy)

include H in
/-- Equality-cap sufficiency: identification is performed before owner
completion, and equal owners make the owner assignment descend. -/
theorem equality_cap_completion {V : Type} [Finite V] (D : RawRecords S V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (owner raw : V → M) (hraw : RawRecords.Hom S D raw)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (x y : V) (hxy : raw x = raw y) (hOwnerXY : E (owner x) (owner y)) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧ f x = f y := by
  classical
  let collapse : V → V := Function.update id x y
  have hRaw (u : V) : raw (collapse u) = raw u := by
    by_cases hu : u = x
    · subst u; simpa only [collapse,Function.update_self] using hxy.symm
    · simp only [collapse,Function.update_of_ne hu,id_eq]
  have hOwner' (u : V) : E (owner (collapse u)) (owner u) := by
    by_cases hu : u = x
    · subst u; simpa only [collapse,Function.update_self] using E.val.symm hOwnerXY
    · simp only [collapse,Function.update_of_ne hu,id_eq]; exact E.val.refl _
  let K := Setoid.ker collapse
  obtain ⟨f,hf,hown,hK⟩ := identified_owner_completion S H D cco E hne word hword owner raw
    hraw hOwner K
    (fun u v h => (hRaw u).symm.trans ((congrArg raw h).trans (hRaw v)))
    (fun u v h => E.val.trans (E.val.symm (hOwner' u))
      (by rw [h]; exact hOwner' v))
  refine ⟨f,hf,hown,hK x y ?_⟩
  change collapse x = collapse y
  by_cases hy : y = x
  · rw [hy]
  · simp only [collapse,Function.update_self,Function.update_of_ne hy,id_eq]

include H in
theorem diversity_cap_completion {V : Type} [Finite V] (D : RawRecords S V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (owner raw : V → M) (hraw : RawRecords.Hom S D raw)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (x y : V) (a : S.Atom () ()) (hxy : S.atomRel a (raw x) (raw y))
    (hCap : ownerSaturate E.val (S.atomRel a) (owner x) (owner y)) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧
      S.atomRel a (f x) (f y) := by
  classical
  have hneXY : x ≠ y := by
    intro hh
    subst y
    exact S.atomRel_ne hxy rfl
  let pair (u v : V) : Prop := (u = x ∧ v = y) ∨ (u = y ∧ v = x)
  have hPair (u v : V) : pair u v ↔ pair v u := by
    constructor <;> rintro (⟨hu,hv⟩ | ⟨hu,hv⟩)
    · exact Or.inr ⟨hv,hu⟩
    · exact Or.inl ⟨hv,hu⟩
    · exact Or.inr ⟨hv,hu⟩
    · exact Or.inl ⟨hv,hu⟩
  let D' : RawRecords S V := {
    edge := fun u v => if pair u v then some a else D.edge u v
    diagonal := fun u => by
      have hn : ¬ pair u u := by
        rintro (⟨hu,hv⟩ | ⟨hu,hv⟩)
        · exact hneXY (hu.symm.trans hv)
        · exact hneXY (hv.symm.trans hu)
      rw [if_neg hn,D.diagonal]
    symmetric := fun u v => by simp only [hPair u v,D.symmetric] }
  have hraw' : RawRecords.Hom S D' raw := by
    intro u v b hb
    dsimp only [D'] at hb
    split_ifs at hb with hp
    · have hab : a = b := Option.some.inj hb
      subst b
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hxy
      · exact (colour_symmetric S _ _).trans hxy
    · exact hraw u v b hb
  have hOwn' : ∀ u v b, D'.edge u v = some b →
      ownerSaturate E.val (S.atomRel b) (owner u) (owner v) := by
    intro u v b hb
    dsimp only [D'] at hb
    split_ifs at hb with hp
    · have hab : a = b := Option.some.inj hb
      subst b
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hCap
      · obtain ⟨z,⟨u,hxu,huz⟩,hzy⟩ := hCap
        exact ⟨u,⟨z,E.val.symm hzy,(colour_symmetric S z u).trans huz⟩,E.val.symm hxu⟩
    · exact hOwner u v b hb
  obtain ⟨f,hf,hown,_⟩ := anchored_completion_of_aligned S H D' cco E hne word hword
    ∅ (by simp [RawRecords.CompleteOn]) owner raw hraw' hOwn' (by simp)
  refine ⟨f,?_,hown,?_⟩
  · intro u v b hb
    by_cases hp : pair u v
    · have hh : S.atomRel a (raw u) (raw v) := by
        rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hxy
        · exact (colour_symmetric S _ _).trans hxy
      have hab : a = b := Option.some.inj (hh.symm.trans (hraw u v b hb))
      subst b
      exact hf u v a (by simp only [D',if_pos hp])
    · exact hf u v b (by simpa only [D',if_neg hp] using hb)
  · exact hf x y a (by simp only [D',if_pos (show pair x y from Or.inl ⟨rfl,rfl⟩)])

def rawSpectrum {V : Type} (D : RawRecords S V) (x y : V) : Set (Option (S.Atom () ())) :=
  {c | ∃ f : V → M, RawRecords.Hom S D f ∧ S.colour (i := ()) (j := ()) (f x) (f y) = c}

def ownerSpectrum {V : Type} (D : RawRecords S V) (E : ColourEq S ())
    (owner : V → M) (x y : V) : Set (Option (S.Atom () ())) :=
  {c | ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ u, E (owner u) (f u)) ∧
    S.colour (i := ()) (j := ()) (f x) (f y) = c}

def colourCap (E : ColourEq S ()) (r s : M) : Set (Option (S.Atom () ())) :=
  {c | ∃ u v, E r u ∧ S.colour (i := ()) (j := ()) u v = c ∧ E v s}

include H in
/-- C10--C11: equality-inclusive exact intersection of the raw spectrum
with the actual owner orbital cap. Equality uses the identified diagram
above; it is never treated as an irreflexive diversity edge. -/
theorem owner_spectrum_eq_inter {V : Type} [Finite V] (D : RawRecords S V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (owner : V → M)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (x y : V) : ownerSpectrum S D E owner x y = rawSpectrum S D x y ∩
      colourCap S E (owner x) (owner y) := by
  ext c
  constructor
  · rintro ⟨f,hf,hown,hcol⟩
    exact ⟨⟨f,hf,hcol⟩,f x,f y,hown x,hcol,E.val.symm (hown y)⟩
  · rintro ⟨⟨raw,hraw,hcol⟩,u,v,hxu,huv,hvy⟩
    cases c with
    | none =>
      have huv' : u = v := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff u v).mp huv
      have hrawXY : raw x = raw y := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff _ _).mp hcol
      obtain ⟨f,hf,hown,hfxy⟩ := equality_cap_completion S H D cco E hne word hword
        owner raw hraw hOwner x y hrawXY (E.val.trans hxu (huv' ▸ hvy))
      exact ⟨f,hf,hown,(S.colour_none_iff _ _).mpr (congrArg (Sigma.mk ()) hfxy)⟩
    | some a =>
      obtain ⟨f,hf,hown,hfxy⟩ := diversity_cap_completion S H D cco E hne word hword
        owner raw hraw hOwner x y a hcol ⟨v,⟨u,hxu,huv⟩,hvy⟩
      exact ⟨f,hf,hown,hfxy⟩

end CCO.OwnerTransversal
