import CCO.Owners.Master.ExactGeometry
import CCO.Owners.Master.RelativeProvider
import CCO.Owners.Master.DiagramCRT

/-! The simultaneous stage invariant uses actual induced finite subsets,
their full original orbital automorphism groups, and ALL original shadows.
Ordinary EPPA is a separate input of the final construction. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

/-- The source hypothesis includes EVERY actual exact quotient, in
particular equality. Each action is the original induced G action. -/
def AllQuotientsEPPA : Prop :=
  ∀ E : Exact S H cco,
    letI := Product.exactInvariant S H cco E
    OrdinaryEPPA G (Quotient E.val)

def originalShadow (T : Set A) (V : Finset (Position S H cco)) :
    Set (Coordinate S H cco V) := coordinateProjection S H cco V '' T

abbrev FiniteStage (U : Finset (Position S H cco)) :=
  Diagram.Stage (exactAmbient S H cco) IsUpset U

variable {U : Finset (Position S H cco)} (B : FiniteStage S H cco U)

def stageQuotient {V W : Finset (Position S H cco)}
    (hV : IsUpset V) (hW : IsUpset W) (hVU : V ⊆ U) (hWV : W ⊆ V) :
    OrbitalQuotient (G := G)
      (Subtype.val : B.B V → Coordinate S H cco V)
      (Subtype.val : B.B W → Coordinate S H cco W) :=
  inducedQuotient (coordinateMap S H cco hWV) (coordinateMap_equivariant S H cco hWV)
    (B.B V) (B.B W) (fun x => B.mapsTo hV hW hVU hWV x.val x.property)
    (B.r_surjective hV hW hVU hWV)

@[simp] theorem stageQuotient_projection {V W : Finset (Position S H cco)}
    (hV : IsUpset V) (hW : IsUpset W) (hVU : V ⊆ U) (hWV : W ⊆ V)
    (x : B.B V) :
    (stageQuotient S H cco B hV hW hVU hWV).projection x = B.r hV hW hVU hWV x := rfl

/-- Every old finite object retains its complete original input, full
ambient packets, ordinary EPPA, and every nested actual finite action. -/
structure Decorations (T : Set A) : Prop where
  contains : ∀ V, IsUpset V → V ⊆ U → originalShadow S H cco T V ⊆ B.B V
  closed : ∀ V, IsUpset V → V ⊆ U →
    FullPacketClosed (quotientSource S H cco (coordinateKernel S H cco V))
      (quotientSource_homogeneous S H cco (coordinateKernel S H cco V)) (B.B V)
  eppa : ∀ V, IsUpset V → V ⊆ U →
    EPPAFor (G := G) (ι := (Subtype.val : B.B V → Coordinate S H cco V))
      {x | x.val ∈ originalShadow S H cco T V}
  m3 : ∀ {V W} (hV : IsUpset V) (hW : IsUpset W) (hVU : V ⊆ U) (hWV : W ⊆ V),
    Function.Surjective (stageQuotient S H cco B hV hW hVU hWV).action ∧
      GroupActions.FibreTransitive (stageQuotient S H cco B hV hW hVU hWV).action
        (B.r hV hW hVU hWV)

structure SourceStage (T : Set A) (U : Finset (Position S H cco)) where
  finite : FiniteStage S H cco U
  decorations : Decorations S H cco finite T
  compatible : finite.CRT.{v,v,z}

/-- Original shadows commute with every canonical quotient projection;
they are actual images of the SAME original input, even when sparse. -/
theorem originalShadow_image (T : Set A)
    {V W : Finset (Position S H cco)} (hWV : W ⊆ V) :
    coordinateMap S H cco hWV '' originalShadow S H cco T V =
      originalShadow S H cco T W := by
  ext y
  constructor
  · rintro ⟨x,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨coordinateProjection S H cco V a,⟨a,ha,rfl⟩,rfl⟩

end
end CCO.Owners.Master
