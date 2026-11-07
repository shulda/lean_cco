import CCO.APRamseyReadout.ActualTupleSupport

/-! C19: the canonical inverse-root map of ANY actual full-code
embedding preserves all original fine names. The proof transports EVERY
selected mixed-spectrum test through the constructed marked-support
embedding; no hidden homogeneity or colour provider is assumed. -/

universe u v w p z
namespace CCO.APRamseyReadout
open CCO.FullCode CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable {A : FiniteInduced (X := B.Point)}
variable (f : Object.Embedding (actualTupleInterpretation B ht F).normal
  ((actualTupleInterpretation B ht F).object A)
  (Object.full (CoordinateTarget B ht) (tupleScheme B ht F)))

def fineImage (a : A.vertices) : Sigma B.Point :=
  (ownerRootEquiv B ht F).symm (f.point a)

@[simp] theorem fineImage_root (a : A.vertices) :
    ownerRoot B ht F (fineImage B ht F f a) = f.point a :=
  (ownerRootEquiv B ht F).apply_symm_apply _

theorem fineImage_sort (a : A.vertices) :
    (fineImage B ht F f a).1 = a.val.1 := by
  have h := (congrArg Root.tag (fineImage_root B ht F f a)).trans (f.tag_eq a)
  exact congrArg ULift.down h

theorem fineImage_injective : Function.Injective (fineImage B ht F f) :=
  (ownerRootEquiv B ht F).symm.injective.comp f.injective

def fineImagePoint (a : A.vertices) : B.Point a.val.1 :=
  Eq.mp (congrArg B.Point (fineImage_sort B ht F f a)) (fineImage B ht F f a).2

private theorem sigma_cast {ι : Type u} {X : ι → Type v}
    (x : Sigma X) {i : ι} (h : x.1 = i) :
    (⟨i,Eq.mp (congrArg X h) x.2⟩ : Sigma X) = x := by
  rcases x with ⟨j,x⟩
  change j = i at h
  cases h
  rfl

@[simp] theorem fineImagePoint_tagged (a : A.vertices) :
    (⟨a.val.1,fineImagePoint B ht F f a⟩ : Sigma B.Point) = fineImage B ht F f a :=
  sigma_cast _ (fineImage_sort B ht F f a)

theorem fineImagePoint_root (a : A.vertices) :
    ownerRoot B ht F ⟨a.val.1,fineImagePoint B ht F f a⟩ = f.point a :=
  (congrArg (ownerRoot B ht F) (fineImagePoint_tagged B ht F f a)).trans
    (fineImage_root B ht F f a)

private theorem root_coordinate_of_eq {L : Language.{u}} {V : Type v}
    {C : Structure L V} {S : RootScheme L} {r s : Root C S} (h : r = s)
    {tag : S.Tag} (hr : r.tag = tag) (hs : s.tag = tag) (j : Fin (S.arity tag)) :
    r.coordinate (hr.symm ▸ j) = s.coordinate (hs.symm ▸ j) := by
  cases h
  rfl

/-- The exact hidden extension sends each original marked coordinate to
the corresponding coordinate of its decoded target owner. -/
theorem fineImage_coordinate (a : A.vertices) (k : Fin (chartArity F a.val.1)) :
    (f.extend (actualTupleInterpretation B ht F).valid
      (actualTupleInterpretation B ht F).valid).point
        ((actualTupleInterpretation B ht F).coordinate a k) =
      (ownerRoot B ht F ⟨a.val.1,fineImagePoint B ht F f a⟩).coordinate k := by
  have h := f.extendPoint_coordinate (actualTupleInterpretation B ht F).valid
    (actualTupleInterpretation B ht F).valid a k
  have hc := root_coordinate_of_eq (fineImagePoint_root B ht F f a) rfl (f.tag_eq a) k
  exact h.trans hc.symm

/-- Equality branches and ALL actual named off-diagonal cylinder tests
are transported by the SAME full induced marked-support embedding. -/
theorem fine_pairEval_transport (a b : A.vertices)
    (k : Fin (chartArity F a.val.1)) (l : Fin (chartArity F b.val.1))
    (test : QuotientPairQF.Formula (cloneSource B)
      (chartSymbol F a.val.1 k).val (chartSymbol F b.val.1 l).val) :
    pairEval B ht (chartCoordinate B ht F a.val.1 k) (chartCoordinate B ht F b.val.1 l)
      (CoordinateTarget B ht)
      ((ownerRoot B ht F ⟨a.val.1,fineImagePoint B ht F f a⟩).coordinate k)
      ((ownerRoot B ht F ⟨b.val.1,fineImagePoint B ht F f b⟩).coordinate l) test ↔
    pairEval B ht (chartCoordinate B ht F a.val.1 k) (chartCoordinate B ht F b.val.1 l)
      (CoordinateTarget B ht) ((ownerRoot B ht F a.val).coordinate k)
      ((ownerRoot B ht F b.val).coordinate l) test := by
  let D := actualTupleInterpretation B ht F
  let g := f.extend D.valid D.valid
  let x := D.coordinate a k
  let y := D.coordinate b l
  have h := pairEval_transport B ht (chartCoordinate B ht F a.val.1 k)
    (chartCoordinate B ht F b.val.1 l) g x y test
  have hi := pairEval_transport B ht (chartCoordinate B ht F a.val.1 k)
    (chartCoordinate B ht F b.val.1 l)
    ((CoordinateTarget B ht).inclusion (D.support A)
      ((CoordinateTarget B ht).isClosed_closure (D.object A).coordinates)) x y test
  have hx : g.point x =
      (ownerRoot B ht F ⟨a.val.1,fineImagePoint B ht F f a⟩).coordinate k :=
    fineImage_coordinate B ht F f a k
  have hy : g.point y =
      (ownerRoot B ht F ⟨b.val.1,fineImagePoint B ht F f b⟩).coordinate l :=
    fineImage_coordinate B ht F f b l
  rw [hx,hy] at h
  exact h.trans hi.symm

/-- Actual B060 singleton recovery, read using every member of the
fixed selected chart on both sides. No selected mixed test is discarded. -/
theorem owner_atom_code_iff {i j : B.Sorts} (x : B.Point i) (y : B.Point j)
    (c : B.source.Atom i j) :
    B.source.atomRel c x y ↔ ∀ k : Fin (chartArity F i), ∀ l : Fin (chartArity F j),
      pairEval B ht (chartCoordinate B ht F i k) (chartCoordinate B ht F j l)
        (CoordinateTarget B ht) ((ownerRoot B ht F ⟨i,x⟩).coordinate k)
        ((ownerRoot B ht F ⟨j,y⟩).coordinate l)
        (QuotientPairQF.membershipFormula (cloneSource B)
          (chartSymbol F i k).val (chartSymbol F j l).val (Sum.inl c)) := by
  have hp (k : Fin (chartArity F i)) (l : Fin (chartArity F j)) :
      pairEval B ht (chartCoordinate B ht F i k) (chartCoordinate B ht F j l)
        (CoordinateTarget B ht) ((ownerRoot B ht F ⟨i,x⟩).coordinate k)
        ((ownerRoot B ht F ⟨j,y⟩).coordinate l)
        (QuotientPairQF.membershipFormula (cloneSource B)
          (chartSymbol F i k).val (chartSymbol F j l).val (Sum.inl c)) ↔
      Sum.inl c ∈ CCO.TransitionClosure.originalTypedQuotientPairSpectrum (cloneSource B)
        (chartSymbol F i k).val (chartSymbol F j l).val
        ((F i).ownerTuple x ((chartEnumeration F i).symm k))
        ((F j).ownerTuple y ((chartEnumeration F j).symm l)) :=
    (pairEval_target B ht _ _ _ _ _).trans
      (QuotientPairQF.membershipFormula_eval (cloneSource B) (cloneHomogeneous B) _ _ _ _ _)
  constructor
  · intro hc k l
    apply (hp k l).mpr
    exact ((F i).original_colour_iff (F j) ht x y c).mpr hc
      ((chartEnumeration F i).symm k) ((chartEnumeration F j).symm l)
  · intro h
    apply ((F i).original_colour_iff (F j) ht x y c).mp
    intro a b
    obtain ⟨k,rfl⟩ := (chartEnumeration F i).symm.surjective a
    obtain ⟨l,rfl⟩ := (chartEnumeration F j).symm.surjective b
    exact (hp k l).mp (h k l)

/-- The canonical root inverse preserves the complete ORIGINAL fine
colour on ALL pairs, including equal roots and different owner sorts. -/
theorem fineReadout_preserves_colours (a b : A.vertices) :
    taggedColour B.source a.val b.val =
      taggedColour B.source (fineImage B ht F f a) (fineImage B ht F f b) := by
  have hcolour : B.source.colour a.val.2 b.val.2 =
      B.source.colour (fineImagePoint B ht F f a) (fineImagePoint B ht F f b) := by
    apply Option.ext
    intro c
    change B.source.atomRel c a.val.2 b.val.2 ↔
      B.source.atomRel c (fineImagePoint B ht F f a) (fineImagePoint B ht F f b)
    rw [owner_atom_code_iff B ht F,owner_atom_code_iff B ht F]
    constructor
    · intro h k l
      exact (fine_pairEval_transport B ht F f a b k l _).mpr (h k l)
    · intro h k l
      exact (fine_pairEval_transport B ht F f a b k l _).mp (h k l)
  have htagged : taggedColour B.source a.val b.val =
      taggedColour B.source ⟨a.val.1,fineImagePoint B ht F f a⟩
        ⟨b.val.1,fineImagePoint B ht F f b⟩ :=
    congrArg (fun q => (⟨a.val.1,b.val.1,q⟩ : CCO.APCharacter.Age.Colour B.source)) hcolour
  exact htagged.trans (congrArg₂ (taggedColour B.source)
    (fineImagePoint_tagged B ht F f a) (fineImagePoint_tagged B ht F f b))

section Host
variable {V : Type z} {C : CCO.UnarySupport.Structure (Sig B ht) V}

/-- One WHOLE actual host embedding realizes every image root together.
The induced fine map is precisely the pre-existing hostOwner map on f. -/
theorem hostFineReadout_preserves_colours (e : C.Embedding (Target B ht))
    (g : Object.Embedding (actualTupleInterpretation B ht F).normal
      ((actualTupleInterpretation B ht F).object A)
      (Object.full (CoordinateModel B ht C) (tupleScheme B ht F))) (a b : A.vertices) :
    taggedColour B.source a.val b.val =
      taggedColour B.source (hostOwner B ht F e (g.point a)) (hostOwner B ht F e (g.point b)) := by
  let h := CCO.TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) e
  let r := Object.rootEmbedding (actualTupleInterpretation B ht F).normal
    (Object.full (CoordinateModel B ht C) (tupleScheme B ht F)) h
  exact fineReadout_preserves_colours B ht F (r.comp g) a b

/-- Actual age membership supplies the SAME single host embedding used
by actualHostOwner; it is not chosen independently for individual roots. -/
theorem actualHostFineReadout_preserves_colours
    (hC : ActualAge B ht C)
    (g : Object.Embedding (actualTupleInterpretation B ht F).normal
      ((actualTupleInterpretation B ht F).object A)
      (Object.full (CoordinateModel B ht C) (tupleScheme B ht F))) (a b : A.vertices) :
    taggedColour B.source a.val b.val =
      taggedColour B.source (actualHostOwner B ht F C hC (g.point a))
        (actualHostOwner B ht F C hC (g.point b)) :=
  hostFineReadout_preserves_colours B ht F (Classical.choice hC.2) g a b

end Host

end
end CCO.APRamseyReadout
