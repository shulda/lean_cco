import CCO.HiddenSAPReadings.Coordinates
import CCO.RawExact.JointLiftingSource
import CCO.UnaryFreshFrames.Age

/-! Actual joint exact quotient lifting on exactly the displayed finite
vertices. The full original RAW kernels are constructed locally; original
semantic CCO discharges the ball-Helly provider. All equivariant unary maps
are preserved by the SAME resulting pair-orbital map. -/
universe u v w r z
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.RawExact
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

theorem finite_coordinate_family_lift [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : Selectors.OriginalNR2 S)
    {I : Type z} [Finite I] (sort : I → OriginalCompletedCoordinateCode S H)
    (source target : ∀ a, CoordinateValue S H (sort a))
    (hPairs : ∀ a b, ∃ g : G,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort a))).act g
        (source a) = target a ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort b))).act g
        (source b) = target b) :
    ∃ e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C,
      (∀ C D (q : CoordinateValue S H C) (r : CoordinateValue S H D), ∃ g : G,
        (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q = e C q ∧
        (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H D)).act g r = e D r) ∧
      ∀ a, e (sort a) (source a) = target a := by
  classical
  letI : Fintype ι := S.finiteSort
  letI (i : ι) : Finite (OriginalNamedHiddenCoordinate S H i) :=
    original_named_hidden_coordinates_finite S H
  letI : Finite (OriginalCompletedCoordinateCode S H) := inferInstance
  letI (C : OriginalCompletedCoordinateCode S H) : MulAction G (CoordinateValue S H C) :=
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).quotientAction
  letI (C : OriginalCompletedCoordinateCode S H) : Countable (CoordinateValue S H C) := inferInstance
  haveI : Countable (Sigma (CoordinateValue S H)) := inferInstance
  let E : ∀ C : OriginalCompletedCoordinateCode S H, NonemptyExact S C.1 C.1 :=
    fun C => (coordinate_kernel_exact S H nr2 C).choose
  have hE : ∀ C, GroupActions.kernel
      (Quotient.mk (originalCompletedCoordinateKernel S H C).val) = evaluate S (E C).words :=
    fun C => (coordinate_kernel_exact S H nr2 C).choose_spec
  have hExt : JointBackAndForth.ExtensionProperty (G := G) (Q := CoordinateValue S H) :=
    JointBackAndForth.graph_one_point_extension S H
      (heterogeneousExactBallHelly_of_CCO S H cco) (CoordinateValue S H) Sigma.fst
      (fun C => Quotient.mk (originalCompletedCoordinateKernel S H C).val)
      (fun _ => Quotient.mk_surjective) (fun _ _ _ => rfl) E hE
  letI : Fintype I := Fintype.ofFinite I
  let row : I → JointBackAndForth.Row (CoordinateValue S H) :=
    fun a => ⟨sort a,source a,target a⟩
  let start : JointBackAndForth.Graph G (CoordinateValue S H) :=
    ⟨Finset.univ.image row,by
      intro p hp q hq
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hq
      exact hPairs a b⟩
  obtain ⟨e,he,hStart⟩ := JointBackAndForth.countable_joint_orbital_automorphism hExt start
  refine ⟨e,he,?_⟩
  intro a
  exact hStart (row a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)

def coordinatePermutation
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C) :
    Equiv.Perm (OriginalCompletedNamedCarrier S H) :=
  (coordinateEquiv S H).symm.trans ((Equiv.sigmaCongrRight e).trans (coordinateEquiv S H))

theorem coordinatePermutation_vertex
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (C : OriginalCompletedCoordinateCode S H) (q : CoordinateValue S H C) :
    coordinatePermutation S H e (coordinateVertex S H C q) =
      coordinateVertex S H C (e C q) := by
  change coordinateEquiv S H
    ((Equiv.sigmaCongrRight e) ((coordinateEquiv S H).symm (coordinateEquiv S H ⟨C,q⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem coordinatePermutation_pair
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : ∀ C D (q : CoordinateValue S H C) (r : CoordinateValue S H D), ∃ g : G,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q = e C q ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H D)).act g r = e D r)
    (x y : OriginalCompletedNamedCarrier S H) :
    ∃ g : G, originalCompletedNamedAct S H g x = coordinatePermutation S H e x ∧
      originalCompletedNamedAct S H g y = coordinatePermutation S H e y := by
  obtain ⟨C,q,hq⟩ := original_completed_coordinate_reading_exists S H x
  obtain ⟨D,r,hr⟩ := original_completed_coordinate_reading_exists S H y
  obtain ⟨g,hgq,hgr⟩ := hPair C D q r
  refine ⟨g,?_,?_⟩
  · rw [← reading_vertex S H hq,coordinatePermutation_vertex,← coordinateVertex_equivariant,hgq]
  · rw [← reading_vertex S H hr,coordinatePermutation_vertex,← coordinateVertex_equivariant,hgr]

/-- Equivariant unary enrichment is a conclusion of pair preservation.
Every function is the actual named map, with its entire global graph. -/
def coordinateAutomorphism (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : ∀ C D (q : CoordinateValue S H C) (r : CoordinateValue S H D), ∃ g : G,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q = e C q ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H D)).act g r = e D r) :
    (originalCompletedStructure S H sap nr2).Aut := by
  refine ⟨coordinatePermutation S H e,?_,?_,?_⟩
  · intro x
    obtain ⟨g,hgx,_⟩ := coordinatePermutation_pair S H e hPair x x
    exact congrArg ULift.up (hgx ▸ original_completed_vertex_sort_invariant S H g x)
  · intro F x
    obtain ⟨g,hgx,hgf⟩ := coordinatePermutation_pair S H e hPair x
      ((originalCompletedStructure S H sap nr2).func F x)
    exact hgf.symm.trans ((original_completed_structure_func_equivariant S H sap nr2 g F.down x).trans
      (congrArg ((originalCompletedStructure S H sap nr2).func F) hgx))
  · intro R xs
    change (Fin 2 → OriginalCompletedNamedCarrier S H) at xs
    obtain ⟨g,hgx,hgy⟩ := coordinatePermutation_pair S H e hPair (xs 0) (xs 1)
    change originalCompletedCylinderBinaryPredicate S H R
      (coordinatePermutation S H e (xs 0)) (coordinatePermutation S H e (xs 1)) ↔ _
    rw [← hgx,← hgy]
    exact original_completed_binary_equivariant S H g R (xs 0) (xs 1)

end
end CCO.HiddenSAPReadings
