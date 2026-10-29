import CCO.RealClosure.SAP.MIIncidence
import CCO.RealClosure.Bounds.SortRestriction

/-! The nonsymmetric elementary theorem is instantiated with the original
symmetric AtomicSource for the exact/terminal Helly branch. The same ambient
G is retained, and actual age SAP is transported, not assumed for a quotient. -/
universe v w t
namespace CCO.RealClosure.SAP
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

def atomicSource : Source.{v,w} M where
  Colour := Option (S.Atom () ())
  finiteColour := by letI := S.finiteAtom () (); infer_instance
  colour := S.colour
  diagonal := fun x y => ((S.colour_none_iff x x).mpr rfl).trans
    ((S.colour_none_iff y y).mpr rfl).symm

theorem atomic_homogeneous (H : HomogeneousSource S G) :
    (atomicSource S).Homogeneous (G := G) where
  preserves := S.colourInvariant_of_homogeneous H
  extends_finite := by
    intro V _ f h hp
    obtain ⟨g,hg⟩ := H.extends_finite_diagram
      (fun x => (⟨(),f x⟩ : Sigma (fun _ : Unit => M)))
      (fun x => (⟨(),h x⟩ : Sigma (fun _ : Unit => M))) (by
        intro x y
        exact congrArg (fun c : Option (S.Atom () ()) =>
          (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j))) (hp x y))
    exact ⟨g,fun x => eq_of_heq (Sigma.mk.inj (hg x)).2⟩

def tag (x : M) : Sigma (fun _ : Unit => M) := ⟨(),x⟩

theorem untag_injective : Function.Injective
    (fun p : Sigma (fun _ : Unit => M) => p.2) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  cases i; cases j
  exact congrArg (fun x => (⟨(),x⟩ : Sigma (fun _ : Unit => M))) h

def taggedPart (A : FinitePart M) : FiniteInduced (X := fun _ : Unit => M) where
  vertices := {p | p.2 ∈ A.vertices}
  finite_vertices := Set.Finite.preimage (untag_injective (M := M)).injOn A.finite_vertices

def untaggedPart (A : FiniteInduced (X := fun _ : Unit => M)) : FinitePart M where
  vertices := (fun p : Sigma (fun _ : Unit => M) => p.2) '' A.vertices
  finite_vertices := A.finite_vertices.image _

def taggedEmbedding {A B : FinitePart M} (e : (atomicSource S).Embedding A B) :
    InducedEmbedding S (taggedPart A) (taggedPart B) where
  toEmbedding := {
    toFun := fun p => ⟨tag (e.toEmbedding ⟨p.val.2,p.property⟩).val,
      (e.toEmbedding ⟨p.val.2,p.property⟩).property⟩
    inj' := by
      intro p q h
      apply Subtype.ext
      apply untag_injective
      have he : e.toEmbedding ⟨p.val.2,p.property⟩ =
          e.toEmbedding ⟨q.val.2,q.property⟩ := by
        apply Subtype.ext
        exact congrArg (fun z : ↥(taggedPart B).vertices => z.val.2) h
      exact congrArg Subtype.val (e.toEmbedding.injective he) }
  preserves_sort := fun p => Unit.ext _ _
  preserves_colours := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩
    cases i; cases j
    exact congrArg (fun c : Option (S.Atom () ()) =>
      (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
        (e.preserves ⟨x,hx⟩ ⟨y,hy⟩)

def untaggedEmbedding {A : FinitePart M}
    {D : FiniteInduced (X := fun _ : Unit => M)}
    (e : InducedEmbedding S (taggedPart A) D) :
    (atomicSource S).Embedding A (untaggedPart D) where
  toEmbedding := {
    toFun := fun x => ⟨(e.toEmbedding ⟨tag x.val,x.property⟩).val.2,
      ⟨(e.toEmbedding ⟨tag x.val,x.property⟩).val,
        (e.toEmbedding ⟨tag x.val,x.property⟩).property,rfl⟩⟩
    inj' := by
      intro x y h
      have he : e.toEmbedding ⟨tag x.val,x.property⟩ =
          e.toEmbedding ⟨tag y.val,y.property⟩ := by
        apply Subtype.ext
        exact untag_injective (congrArg Subtype.val h)
      have hv := congrArg (fun z : ↥(taggedPart A).vertices => z.val.2)
        (e.toEmbedding.injective he)
      exact Subtype.ext hv }
  preserves := by
    intro x y
    exact congrArg (fun c : Σ i : Unit, Σ j : Unit, Option (S.Atom i j) =>
      match c with | ⟨(),(),a⟩ => a)
      (e.preserves_colours ⟨tag x.val,x.property⟩ ⟨tag y.val,y.property⟩)

theorem atomic_sap (sap : AgeSAP S) : (atomicSource S).AgeSAP where
  amalgamate := by
    intro A B C eAB eAC
    obtain ⟨D,eBD,eCD,hbase,hstrong⟩ := sap.strong_amalgamate
      (taggedPart A) (taggedPart B) (taggedPart C)
      (taggedEmbedding S eAB) (taggedEmbedding S eAC)
    refine ⟨untaggedPart D,untaggedEmbedding S eBD,untaggedEmbedding S eCD,?_,?_⟩
    · intro a
      apply Subtype.ext
      exact congrArg (fun z : ↥D.vertices => z.val.2) (hbase ⟨tag a.val,a.property⟩)
    · intro b c he
      have he' : eBD.toEmbedding ⟨tag b.val,b.property⟩ =
          eCD.toEmbedding ⟨tag c.val,c.property⟩ := by
        apply Subtype.ext
        exact untag_injective (congrArg Subtype.val he)
      obtain ⟨a,ha,hc⟩ := hstrong ⟨tag b.val,b.property⟩ ⟨tag c.val,c.property⟩ he'
      refine ⟨⟨a.val.2,a.property⟩,?_,?_⟩
      · apply Subtype.ext
        exact congrArg (fun z : ↥(taggedPart B).vertices => z.val.2) ha
      · apply Subtype.ext
        exact congrArg (fun z : ↥(taggedPart C).vertices => z.val.2) hc

def invariantColourIso (H : HomogeneousSource S G) :
    InvariantEq G M ≃o ColourEq S () where
  toFun E := ⟨E.val,by
    intro x y x' y' hc
    obtain ⟨g,hg,hg'⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
    rw [← hg,← hg']
    exact (InvariantEq.apply_smul_iff E g x y).symm⟩
  invFun E := ⟨E.val,fun g x y h =>
    (E.property x y (g • x) (g • y) (S.colourInvariant_of_homogeneous H g x y).symm).mp h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end CCO.RealClosure.SAP
