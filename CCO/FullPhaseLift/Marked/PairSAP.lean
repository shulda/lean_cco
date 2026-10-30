import CCO.PairSafeSplit.SAP.Source
import CCO.FullPhaseLift.BinarySource.SourceSpan

/-! Strong spans in the ACTUAL legal marked-pair chart age. The marked
source is the B047 source obtained from its internally proved old-reduct
identification. Its SAP comes from old SAP, never from an arbitrary global
homogeneous seed marking. -/

universe u v w t
namespace CCO.FullPhaseLift.Marked
open APCharacter APCharacter.SourceAge APCharacter.SourceAge.UnarySource
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour
open scoped FirstOrder
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

abbrev PairEmbedding {mask : MaskData S} (A B : Age.Chart S mask) :=
  @FirstOrder.Language.Embedding (Age.Language S) (Fin A.size) (Fin B.size)
    A.structure B.structure

def PairStrongAmalgamation (mask : MaskData S) : Prop :=
  ∀ (A B C : Age.Chart S mask) (f : PairEmbedding S A B) (g : PairEmbedding S A C),
    ∃ (Z : Age.Chart S mask) (l : PairEmbedding S B Z) (r : PairEmbedding S C Z),
      (∀ x, l (f x) = r (g x)) ∧
      ∀ x y, l x = r y → ∃ a, f a = x ∧ g a = y

variable {S}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {mask : MaskData S}
variable {completion : Age.CompletionProperty S mask}
variable (I : Identification S H completion)

def actualPairTable : Age.Table S (NewPoint I) where
  owner p := Age.ownerEquiv S (childLabel I p.1)
  colour p q := Age.colourEquiv S (eraseColour I (taggedColour (UnarySource.source I) p q))

theorem actualPairTable_realized : Age.Realized S mask (actualPairTable I) := by
  refine ⟨oldEquiv I,mark I ∘ oldEquiv I,(oldEquiv I).injective,?_,?_⟩
  · exact ⟨fun p => (global_marking I).1 _,fun p q => (global_marking I).2 _ _⟩
  · apply congrArg₂ Table.mk
    · funext p
      change Age.ownerEquiv S (childLabel I p.1) =
        Age.ownerEquiv S ((oldEquiv I p).1,mark I (oldEquiv I p))
      rw [PairSafeSplit.SAP.mark_oldEquiv]
      rfl
    · funext p q
      exact congrArg (Age.colourEquiv S) (erase_tagged I p q)

theorem chart_in_actual_source (C : Age.Chart S mask) :
    ∃ p : Fin C.size ↪ NewPoint I,
      (∀ x, (actualPairTable I).owner (p x) = C.table.owner x) ∧
      ∀ x y, (actualPairTable I).colour (p x) (p y) = C.table.colour x y := by
  obtain ⟨f,ho,hc⟩ := Age.chart_names S H completion C
  let p := f.trans (newEquiv I).symm.toEmbedding
  have hp : ∀ x, newEquiv I (p x) = f x := fun x => (newEquiv I).apply_symm_apply _
  refine ⟨p,?_,?_⟩
  · intro x
    change Age.ownerEquiv S (childLabel I (p x).1) = _
    rw [← new_owner,hp]
    exact ho x
  · intro x y
    change Age.colourEquiv S (eraseColour I (taggedColour (UnarySource.source I) (p x) (p y))) = _
    rw [← new_colour,hp,hp]
    exact hc x y

theorem actualPairTable_reflects (p q r s : NewPoint I)
    (hp : (actualPairTable I).owner p = (actualPairTable I).owner r)
    (hq : (actualPairTable I).owner q = (actualPairTable I).owner s)
    (hc : (actualPairTable I).colour p q = (actualPairTable I).colour r s) :
    taggedColour (UnarySource.source I) p q = taggedColour (UnarySource.source I) r s := by
  apply PairSafeSplit.SAP.tagged_colour_of_old I p q r s
  · exact childLabel_injective I ((Age.ownerEquiv S).injective hp)
  · exact childLabel_injective I ((Age.ownerEquiv S).injective hq)
  · have he := (Age.colourEquiv S).injective hc
    simpa only [erase_tagged] using he

theorem actualPairTable_preserves {p q r s : NewPoint I}
    (hc : taggedColour (UnarySource.source I) p q = taggedColour (UnarySource.source I) r s) :
    (actualPairTable I).owner p = (actualPairTable I).owner r ∧
      (actualPairTable I).colour p q = (actualPairTable I).colour r s := by
  constructor
  · exact congrArg (fun c => Age.ownerEquiv S (childLabel I c.1)) hc
  · exact congrArg (fun c => Age.colourEquiv S (eraseColour I c)) hc

theorem pairStrongAmalgamation_of_source_sap (sap : AgeSAP (UnarySource.source I)) :
    PairStrongAmalgamation S mask := by
  intro A B C f g
  letI := A.structure
  letI := B.structure
  letI := C.structure
  obtain ⟨p,hpo,hpc⟩ := chart_in_actual_source I B
  obtain ⟨q,hqo,hqc⟩ := chart_in_actual_source I C
  have hf := A.table.embedding_preserves B.table f
  have hg := A.table.embedding_preserves C.table g
  have names : ∀ x y,
      taggedColour (UnarySource.source I) (p (f x)) (p (f y)) =
        taggedColour (UnarySource.source I) (q (g x)) (q (g y)) := by
    intro x y
    apply actualPairTable_reflects I
    · exact (hpo (f x)).trans ((hf.1 x).trans ((hg.1 x).symm.trans (hqo (g x)).symm))
    · exact (hpo (f y)).trans ((hf.1 y).trans ((hg.1 y).symm.trans (hqo (g y)).symm))
    · exact (hpc (f x) (f y)).trans
        ((hf.2 x y).trans ((hg.2 x y).symm.trans (hqc (g x) (g y)).symm))
  obtain ⟨V,hV,j,k,target,comm,inter,hleft,hright,cover⟩ :=
    BinarySource.strict_pair_span (UnarySource.source I) sap p q f.toEmbedding g.toEmbedding names
  letI : Finite V := hV
  letI : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let targetF : Fin (Fintype.card V) ↪ NewPoint I := e.symm.toEmbedding.trans target
  let jF : Fin B.size ↪ Fin (Fintype.card V) := j.trans e.toEmbedding
  let kF : Fin C.size ↪ Fin (Fintype.card V) := k.trans e.toEmbedding
  let T : Age.Table S (Fin (Fintype.card V)) := Age.reindex S (actualPairTable I) targetF
  have hT : Age.Realized S mask T := Age.realized_reindex S (actualPairTable_realized I) targetF
  let Z : Age.Chart S mask := ⟨Fintype.card V,T,hT⟩
  have hj (x : Fin B.size) : targetF (jF x) = target (j x) := e.symm_apply_apply (j x) ▸ rfl
  have hk (x : Fin C.size) : targetF (kF x) = target (k x) := e.symm_apply_apply (k x) ▸ rfl
  let l : PairEmbedding S B Z := B.table.embedding T jF
    (fun x => by
      change (actualPairTable I).owner (targetF (jF x)) = _
      rw [hj]
      exact ((actualPairTable_preserves I (hleft x x)).1).symm.trans (hpo x))
    (fun x y => by
      change (actualPairTable I).colour (targetF (jF x)) (targetF (jF y)) = _
      rw [hj,hj]
      exact ((actualPairTable_preserves I (hleft x y)).2).symm.trans (hpc x y))
  let r : PairEmbedding S C Z := C.table.embedding T kF
    (fun x => by
      change (actualPairTable I).owner (targetF (kF x)) = _
      rw [hk]
      exact ((actualPairTable_preserves I (hright x x)).1).symm.trans (hqo x))
    (fun x y => by
      change (actualPairTable I).colour (targetF (kF x)) (targetF (kF y)) = _
      rw [hk,hk]
      exact ((actualPairTable_preserves I (hright x y)).2).symm.trans (hqc x y))
  refine ⟨Z,l,r,?_,?_⟩
  · intro x
    exact congrArg e (comm x)
  · intro x y hxy
    exact inter x y (e.injective hxy)

variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}

/-- B047 supplies the ACTUAL strong marked-pair span, after its internally
constructed old-reduct identification. Only original pair SAP is input. -/
theorem actual_pairStrongAmalgamation [∀ i, Countable (X i)]
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S) (sap : AgeSAP S) :
    PairStrongAmalgamation S P.masks := by
  let I := SourceAge.actualIdentification P cco
  exact pairStrongAmalgamation_of_source_sap I (PairSafeSplit.SAP.unary_source_sap P cco I sap)

end
end CCO.FullPhaseLift.Marked
