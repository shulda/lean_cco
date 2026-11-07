import CCO.APRamseyReadout.ActualTupleSupport
import CCO.APRamseyReadout.FineReadout
import CCO.APRamseyReadout.TupleReadout
import CCO.FullCode.Cofinality
import CCO.FullCode.StructureTransport

/-! The actual arbitrary-host source instance. ONE whole induced hidden
embedding realizes ALL valid tuples in the owner structure. Their exact
coordinate-generated support factors back through that SAME embedding;
no assumption that the host is root-generated excludes orphan inputs. -/

universe u v w p z
namespace CCO.APRamseyReadout
open CCO.FullCode CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable {W : Type z} {C : CCO.UnarySupport.Structure (Sig B ht) W}

abbrev hostBinaryEmbedding (e : C.Embedding (Target B ht)) :=
  CCO.TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) e

/-- The complete finite old object contains exactly the owners of ALL
valid host tuples, using the one supplied whole-host realization. -/
def hostAOfEmbedding [Finite W] (e : C.Embedding (Target B ht)) :
    CCO.FiniteInduced (X := B.Point) where
  vertices := Set.range (hostOwner B ht F e)
  finite_vertices := Set.finite_range _

def hostRootEquiv [Finite W] (e : C.Embedding (Target B ht)) :
    Root (CoordinateModel B ht C) (tupleScheme B ht F) ≃
      (hostAOfEmbedding B ht F e).vertices :=
  Equiv.ofInjective (hostOwner B ht F e) (hostOwner_injective B ht F e)

@[simp] theorem hostRootEquiv_owner [Finite W] (e : C.Embedding (Target B ht))
    (r : Root (CoordinateModel B ht C) (tupleScheme B ht F)) :
    (hostRootEquiv B ht F e r).val = hostOwner B ht F e r := rfl

/-- All generated support points remain in the actual image of the
same whole embedding, because its image is unary-closed. -/
theorem hostSupport_in_range [Finite W] (e : C.Embedding (Target B ht)) :
    (actualTupleInterpretation B ht F).support (hostAOfEmbedding B ht F e) ⊆
      Set.range (hostBinaryEmbedding B ht e).point := by
  have hroot (r : Root (CoordinateModel B ht C) (tupleScheme B ht F)) :
      ∀ j, (ownerRoot B ht F (hostOwner B ht F e r)).coordinate j ∈
        Set.range (hostBinaryEmbedding B ht e).point := by
    rw [ownerRoot_hostOwner]
    intro j
    exact ⟨r.coordinate j,rfl⟩
  apply (CoordinateTarget B ht).closure_minimal (hostBinaryEmbedding B ht e).range_closed
  rintro y ⟨⟨a,⟨r,ha⟩⟩,j,hj⟩
  subst a
  exact hj ▸ hroot r j

def hostSupportEmbedding [Finite W] (e : C.Embedding (Target B ht)) :
    Structure.Embedding
      ((actualTupleInterpretation B ht F).supportStructure (hostAOfEmbedding B ht F e))
      (CoordinateModel B ht C) :=
  ((CoordinateTarget B ht).inclusion
    ((actualTupleInterpretation B ht F).support (hostAOfEmbedding B ht F e))
    ((CoordinateTarget B ht).isClosed_closure _)).factor (hostBinaryEmbedding B ht e)
      (by rintro _ ⟨x,rfl⟩; exact hostSupport_in_range B ht F e x.property)

@[simp] theorem hostSupportEmbedding_point [Finite W] (e : C.Embedding (Target B ht))
    (x : (actualTupleInterpretation B ht F).support (hostAOfEmbedding B ht F e)) :
    (hostBinaryEmbedding B ht e).point ((hostSupportEmbedding B ht F e).point x) = x.val := by
  exact Structure.Embedding.factorPoint_spec
    ((CoordinateTarget B ht).inclusion
      ((actualTupleInterpretation B ht F).support (hostAOfEmbedding B ht F e))
      ((CoordinateTarget B ht).isClosed_closure _))
    (hostBinaryEmbedding B ht e)
    (by rintro _ ⟨y,rfl⟩; exact hostSupport_in_range B ht F e y.property) x

/-- Every original literal coordinate is recovered, including tags and
all repeated-coordinate equalities, rather than a new compatible tuple. -/
theorem hostSupportEmbedding_root [Finite W] (e : C.Embedding (Target B ht))
    (r : Root (CoordinateModel B ht C) (tupleScheme B ht F)) :
    (((actualTupleInterpretation B ht F).object (hostAOfEmbedding B ht F e)).markedRoot
        (hostRootEquiv B ht F e r)).map (hostSupportEmbedding B ht F e) = r := by
  apply Root.map_injective (hostBinaryEmbedding B ht e)
  calc
    _ = ownerRoot B ht F (hostOwner B ht F e r) := by
      refine Root.ext_coordinates
        (r := ((((actualTupleInterpretation B ht F).object (hostAOfEmbedding B ht F e)).markedRoot
          (hostRootEquiv B ht F e r)).map (hostSupportEmbedding B ht F e)).map
            (hostBinaryEmbedding B ht e))
        (s := ownerRoot B ht F (hostOwner B ht F e r)) (by rfl) ?_
      intro j
      change (hostBinaryEmbedding B ht e).point
        ((hostSupportEmbedding B ht F e).point
          ((actualTupleInterpretation B ht F).coordinate (hostRootEquiv B ht F e r) j)) =
        (ownerRoot B ht F (hostOwner B ht F e r)).coordinate j
      exact hostSupportEmbedding_point B ht F e _
    _ = r.map (hostBinaryEmbedding B ht e) := ownerRoot_hostOwner B ht F e r

/-- A fully constructed actual owner image and its SAME-host order
readout. The arbitrary source host may contain any number of orphans. -/
structure HostReadout (C : CCO.UnarySupport.Structure (Sig B ht) W) [LinearOrder W] where
  embedding : C.Embedding (Target B ht)
  old : CCO.FiniteInduced (X := B.Point)
  vertices_eq : old.vertices = Set.range (hostOwner B ht F embedding)
  roots : Root (CoordinateModel B ht C) (tupleScheme B ht F) ≃ old.vertices
  roots_owner : ∀ r, (roots r).val = hostOwner B ht F embedding r
  support : Structure.Embedding
    ((actualTupleInterpretation B ht F).supportStructure old) (CoordinateModel B ht C)
  support_root : ∀ r,
    (((actualTupleInterpretation B ht F).object old).markedRoot (roots r)).map support = r
  readout : (actualTupleInterpretation B ht F).ReadoutOn old
  order_iff : ∀ x y,
    (actualTupleInterpretation B ht F).ReadoutComparison readout x y ↔ support.point x < support.point y

def hostReadoutOfEmbedding [Finite W] [LinearOrder W] (e : C.Embedding (Target B ht)) :
    HostReadout B ht F C where
  embedding := e
  old := hostAOfEmbedding B ht F e
  vertices_eq := rfl
  roots := hostRootEquiv B ht F e
  roots_owner := hostRootEquiv_owner B ht F e
  support := hostSupportEmbedding B ht F e
  support_root := hostSupportEmbedding_root B ht F e
  readout := ⟨LinearOrder.lift' (hostSupportEmbedding B ht F e).point
    (hostSupportEmbedding B ht F e).injective⟩
  order_iff _ _ := Iff.rfl

/-- The public source constructor discharges the whole realization
from actual age membership; no embedding or completion callback remains. -/
def actualHostReadout (C : CCO.UnarySupport.Structure (Sig B ht) W) [LinearOrder W]
    (hC : ActualAge B ht C) : HostReadout B ht F C := by
  letI : Finite W := hC.1
  exact hostReadoutOfEmbedding B ht F (Classical.choice hC.2)


namespace HostReadout
variable [LinearOrder W] (R : HostReadout B ht F C)

/-- The full marked code on the actual owner image is the complete code
of ALL host roots. This is constructed from the genuine support embedding,
not by assuming preservation of the visible predicates. -/
def codeToHost : Object.Embedding (actualTupleInterpretation B ht F).normal
    ((actualTupleInterpretation B ht F).object R.old)
    (Object.full (CoordinateModel B ht C) (tupleScheme B ht F)) :=
  (Object.rootEmbedding (actualTupleInterpretation B ht F).normal
    ((actualTupleInterpretation B ht F).object R.old).markedObject R.support).comp
      (Object.marking (actualTupleInterpretation B ht F).normal
        ((actualTupleInterpretation B ht F).object R.old))

@[simp] theorem codeToHost_point (a : R.old.vertices) :
    (codeToHost B ht F R).point a = R.roots.symm a := by
  change (((actualTupleInterpretation B ht F).object R.old).markedRoot a).map R.support = _
  simpa only [Equiv.apply_symm_apply] using R.support_root (R.roots.symm a)

theorem codeToHost_surjective : Function.Surjective (codeToHost B ht F R).point := by
  intro r
  refine ⟨R.roots r,?_⟩
  rw [codeToHost_point,Equiv.symm_apply_apply]

/-- C19 on the actual finite owner image: a full visible code map gives
an original induced map into the SAME packet, at exactly its image roots.
Fine-colour reflection is discharged by all actual mixed spectrum tests. -/
def fineEmbedding {A : CCO.FiniteInduced (X := B.Point)}
    (f : Object.Embedding (actualTupleInterpretation B ht F).normal
      ((actualTupleInterpretation B ht F).object A)
      (Object.full (CoordinateModel B ht C) (tupleScheme B ht F))) :
    CCO.InducedEmbedding B.source A R.old where
  toEmbedding := ⟨fun a => R.roots (f.point a),R.roots.injective.comp f.injective⟩
  preserves_sort a :=
    (congrArg Sigma.fst (R.roots_owner (f.point a))).trans
      ((hostOwner_tag B ht F R.embedding (f.point a)).trans
        (congrArg ULift.down (f.tag_eq a)))
  preserves_colours a b := by
    change CCO.taggedColour B.source a.val b.val =
      CCO.taggedColour B.source (R.roots (f.point a)).val (R.roots (f.point b)).val
    rw [R.roots_owner,R.roots_owner]
    exact hostFineReadout_preserves_colours B ht F R.embedding f a b

@[simp] theorem fineEmbedding_point {A : CCO.FiniteInduced (X := B.Point)}
    (f : Object.Embedding (actualTupleInterpretation B ht F).normal
      ((actualTupleInterpretation B ht F).object A)
      (Object.full (CoordinateModel B ht C) (tupleScheme B ht F))) (a : A.vertices) :
    (fineEmbedding B ht F R f).toEmbedding a = R.roots (f.point a) := rfl

end HostReadout

end
end CCO.APRamseyReadout
