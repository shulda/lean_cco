import CCO.HiddenSAPReadings.PairOrbitals
import CCO.UnaryFreshFrames.Age

/-! Completed canonical binary members: a homomorphism is induced.
The separate tuple statement at the end requires its explicit canonical
tuple completion and is not a premise of the binary result. -/
universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.UnaryTermsReturn CCO.TypedOrbitFrames
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (nr2 : Selectors.OriginalNR2 S)

/-- A homomorphism on actual completed induced closed members. Injection
and reflection are conclusions, not fields. -/
structure CompletedHom (A : (originalCompletedStructure S H sap nr2).Piece)
    (T : Set (OriginalCompletedNamedCarrier S H)) where
  point : A.points → OriginalCompletedNamedCarrier S H
  mem_point : ∀ x, point x ∈ T
  sort_eq : ∀ x, (originalCompletedStructure S H sap nr2).sort (point x) =
    (originalCompletedStructure S H sap nr2).sort x.val
  func_eq : ∀ F x, point (A.func F x) =
    (originalCompletedStructure S H sap nr2).func F (point x)
  preserves : ∀ R (xs : Fin 2 → A.points),
    originalCompletedCylinderBinaryPredicate S H R (xs 0).val (xs 1).val →
    originalCompletedCylinderBinaryPredicate S H R (point (xs 0)) (point (xs 1))

namespace CompletedHom
variable {S H sap nr2}
variable {A : (originalCompletedStructure S H sap nr2).Piece}
variable {T : Set (OriginalCompletedNamedCarrier S H)}

theorem injective (f : CompletedHom S H sap nr2 A T) : Function.Injective f.point := by
  intro x y h
  by_contra hxy
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap x.val y.val hval
  let xs : Fin 2 → A.points := ![x,y]
  have hMove := f.preserves R xs hR
  exact hMove.1 h

theorem reflects (f : CompletedHom S H sap nr2 A T)
    (R : OriginalCompletedCylinderBinaryName S H) (x y : A.points)
    (h : originalCompletedCylinderBinaryPredicate S H R (f.point x) (f.point y)) :
    originalCompletedCylinderBinaryPredicate S H R x.val y.val := by
  have hxy : x.val ≠ y.val := by
    intro e
    exact h.1 (congrArg f.point (Subtype.ext e))
  obtain ⟨P,hP⟩ := original_completed_distinct_pair_binary_exists S H sap x.val y.val hxy
  have hP' := f.preserves P ![x,y] hP
  obtain ⟨g,hgx,hgy⟩ := same_binary_motion S H P hP hP'
  apply (original_completed_binary_equivariant S H g R x.val y.val).mp
  rwa [hgx,hgy]

/-- Source rigidity result on the actual binary envelope. -/
def toEmbedding (f : CompletedHom S H sap nr2 A T) : A.Embedding T where
  point := f.point
  mem_point := f.mem_point
  injective := f.injective
  sort_eq := f.sort_eq
  func_eq := f.func_eq
  rel_iff R xs := by
    change (Fin 2 → A.points) at xs
    exact ⟨fun h => f.reflects R (xs 0) (xs 1) h,
      fun h => f.preserves R xs h⟩

/-- Injection reflects every literal graph identity of the total named
functions; there is no partial-domain completion choice. -/
theorem func_graph_iff (f : CompletedHom S H sap nr2 A T) (F) (x y : A.points) :
    (originalCompletedStructure S H sap nr2).func F (f.point x) = f.point y ↔
      A.func F x = y := by
  rw [← f.func_eq]
  exact f.injective.eq_iff

end CompletedHom

/-- Separate A08 interface: each compatible tuple's entire old diagram
is encoded by its canonical type. It is not supplied by binary colours. -/
structure CanonicalTupleCompletion (V : Type*) (n : ℕ) where
  TypeName : Type*
  typeOf : (Fin n → V) → TypeName

namespace CanonicalTupleCompletion
variable {V W : Type*} {n : ℕ}

def predicate (K : CanonicalTupleCompletion V n) (t : K.TypeName)
    (xs : Fin n → V) : Prop := K.typeOf xs = t

/-- Preserving all complete tuple predicates forces equality of type,
hence reflection of EVERY relation decoded from that whole type. -/
theorem reflects_decoded (K : CanonicalTupleCompletion V n) (f : V → V)
    (preserves : ∀ t xs, K.predicate t xs → K.predicate t (f ∘ xs))
    (R : K.TypeName → Prop) (xs : Fin n → V) :
    R (K.typeOf (f ∘ xs)) ↔ R (K.typeOf xs) := by
  have he := preserves (K.typeOf xs) xs rfl
  rw [show K.typeOf (f ∘ xs) = K.typeOf xs from he]

end CanonicalTupleCompletion
end
end CCO.HiddenSAPReadings
