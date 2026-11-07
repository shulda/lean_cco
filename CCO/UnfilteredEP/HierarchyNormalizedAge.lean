import CCO.UnfilteredEP.HierarchyMaps
import CCO.APRamseyReadout.ProperHiddenJEP

/-!
# B064 C45--C48: the ONE actual normalized proper hidden class

Membership means the complete actual proper hidden object, with a fixed
hidden sort priority and a strictly fixed hierarchical order. Functions,
partial domains and semantic cylinders stay exactly those of the actual
source. The same class is used by Ramsey, JEP and relative reset tasks.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

/-- The actual normalized hidden class, with no root-generation or
no-orphan restriction and with the entire old unary signature retained. -/
def NormalizedProperAge
    (A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)) : Prop :=
  ∃ (C : CCO.UnarySupport.Structure (Sig B ht) A.Carrier) (o : LinearOrder A.Carrier)
    (hC : ActualAge B ht C) (proper : ∀ x, ProperSort B ht (C.sort x)),
      hierarchicalOrder B ht C proper hC priority o = o ∧
        A.model = @OrderedCoordinateModel B ht A.Carrier C o

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (proper : ∀ x, ProperSort B ht (C.sort x)) (hC : ActualAge B ht C)

def normalizedCoordinateModel (o : LinearOrder V) :
    Structure (OrderedCoordinateLanguage B ht) V :=
  @OrderedCoordinateModel B ht V C (hierarchicalOrder B ht C proper hC priority o)

/-- One normalization acts on exactly the old finite carrier. -/
def normalizedHiddenObject [Finite V] (o : LinearOrder V) :
    FiniteHidden (OrderedCoordinateLanguage B ht) :=
  ⟨V,normalizedCoordinateModel B ht priority C proper hC o,inferInstance⟩

theorem normalizedHiddenObject_mem [Finite V] (o : LinearOrder V) :
    NormalizedProperAge B ht priority (normalizedHiddenObject B ht priority C proper hC o) :=
  ⟨C,hierarchicalOrder B ht C proper hC priority o,hC,proper,
    hierarchicalOrder_idempotent B ht C proper hC priority o,rfl⟩

theorem normalizedProperAge_to_proper
    {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
    (hA : NormalizedProperAge B ht priority A) : ProperOrderedAge B ht A := by
  obtain ⟨C,o,hC,proper,hfixed,heq⟩ := hA
  refine ⟨⟨C,o,hC,heq⟩,?_⟩
  intro x
  rw [heq]
  exact proper x

include proper hC in
/-- Every actual unexpanded finite object has a normalized expansion.
The input order is arbitrary and its normalization is legal. -/
theorem proper_normalized_expansion_exists [Finite V] :
    ∃ o : LinearOrder V,
      NormalizedProperAge B ht priority ⟨V,@OrderedCoordinateModel B ht V C o,inferInstance⟩ := by
  letI := Fintype.ofFinite V
  let o : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  exact ⟨hierarchicalOrder B ht C proper hC priority o,
    normalizedHiddenObject_mem B ht priority C proper hC o⟩

variable {W : Type a} {D : CCO.UnarySupport.Structure (Sig B ht) W}
variable (properD : ∀ x, ProperSort B ht (D.sort x)) (hD : ActualAge B ht D)

/-- The actual ALL-map normalization: every given full ordered induced
embedding keeps exactly its point map, unary graphs and semantic types. -/
def normalizedOrderedEmbedding (oC : LinearOrder V) (oD : LinearOrder W)
    (e : Structure.Embedding (@OrderedCoordinateModel B ht V C oC)
      (@OrderedCoordinateModel B ht W D oD)) :
    Structure.Embedding (normalizedCoordinateModel B ht priority C proper hC oC)
      (normalizedCoordinateModel B ht priority D properD hD oD) := by
  letI := oC
  letI := oD
  let raw := CCO.TerminalHiddenHN.orderedEmbeddingInverse (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) e
  refine {
    point := e.point
    injective := e.injective
    sort_eq := e.sort_eq
    map_func := e.map_func
    reflect_func := e.reflect_func
    unary_iff := fun U => PEmpty.elim U
    binary_iff := ?_ }
  intro R x y
  cases R with
  | inl R => exact e.binary_iff (.inl R) x y
  | inr p =>
    change (D.sort (e.point x) = p.1 ∧ D.sort (e.point y) = p.2 ∧
      @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT (e.point x) (e.point y)) ↔
      (C.sort x = p.1 ∧ C.sort y = p.2 ∧
        @LT.lt _ (hierarchicalOrder B ht C proper hC priority oC).toLT x y)
    have hx : D.sort (e.point x) = C.sort x := e.sort_eq x
    have hy : D.sort (e.point y) = C.sort y := e.sort_eq y
    rw [hx,hy]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (hierarchicalOrder_map_iff B ht hC hD raw.toEmbedding oC oD raw.order_iff
        proper properD priority x y))

@[simp] theorem normalizedOrderedEmbedding_point (oC : LinearOrder V) (oD : LinearOrder W)
    (e : Structure.Embedding (@OrderedCoordinateModel B ht V C oC)
      (@OrderedCoordinateModel B ht W D oD)) (x : V) :
    (normalizedOrderedEmbedding B ht priority C proper hC properD hD oC oD e).point x = e.point x := rfl

end
end CCO.UnfilteredEP
