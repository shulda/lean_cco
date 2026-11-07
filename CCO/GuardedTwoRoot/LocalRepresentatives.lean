import CCO.HiddenSAPReadings.PartialSplitting
import CCO.GuardedTwoRoot.RepresentativeTerms

/-! Source14 C13. Split ONE vetted complete local source factor. The
old real positions and the designated representatives of EVERY old
proper position are simultaneously distinct in one actual finite old
world. This does not posit a completion of any larger partial source. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- Literal real identity or the actual named proper quotient class.
This relation names no new unary map and chooses no global section. -/
def RealRepresents (a : Sigma X) (x : OriginalCompletedNamedCarrier S H) : Prop :=
  x = .inl a ∨ ∃ D : OriginalNamedHiddenCoordinate S H a.1,
    x = originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val a.2)

namespace SplitAssignment
variable {S H} {P : Type z} {f : P → OriginalCompletedNamedCarrier S H}
variable {A : Set (Sigma X)} (r : SplitAssignment S H f A)

theorem real_value (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (p : P) (hp : IsRealPosition S H f p) : ∃ a : Sigma X, r.point p = .inl a := by
  obtain ⟨a,ha⟩ := hp
  have hs : (originalCompletedStructure S H sap nr2).sort (r.point p) = ⟨⟨a.1,.inl ()⟩⟩ := by
    change ULift.up (originalCompletedVertexSort S H (r.point p)) = _
    rw [r.sort_eq p,ha]
    cases a
    rfl
  obtain ⟨x,hx⟩ := original_completed_real_carrier_exists S H sap nr2 ⟨r.point p,hs⟩
  exact ⟨⟨a.1,x⟩,hx⟩

def allRepresentatives (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (p : P) : Sigma X := by
  classical
  exact if hp : IsRealPosition S H f p then ((SplitAssignment.real_value r) sap nr2 p hp).choose
  else r.representative ⟨p,hp⟩

theorem allRepresentatives_real (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {p : P} (hp : IsRealPosition S H f p) :
    r.point p = .inl ((SplitAssignment.allRepresentatives r) sap nr2 p) := by
  dsimp only [allRepresentatives]
  rw [dif_pos hp]
  exact ((SplitAssignment.real_value r) sap nr2 p hp).choose_spec

theorem allRepresentatives_proper (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {p : P} (hp : ¬ IsRealPosition S H f p) :
    (SplitAssignment.allRepresentatives r) sap nr2 p = r.representative ⟨p,hp⟩ := dif_neg hp

theorem allRepresentatives_reads (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (p : P) :
    RealRepresents S H ((SplitAssignment.allRepresentatives r) sap nr2 p) (r.point p) := by
  by_cases hp : IsRealPosition S H f p
  · exact Or.inl ((SplitAssignment.allRepresentatives_real r) sap nr2 hp)
  · rw [(SplitAssignment.allRepresentatives_proper r) sap nr2 hp,r.proper_fixed p hp]
    let q : ProperPosition S H f := ⟨p,hp⟩
    let req := properPositionRequest S H f q
    obtain ⟨a,ha,hclass⟩ := r.representative_class q
    change RealRepresents S H (r.representative q) (f p)
    rw [ha]
    right
    refine ⟨req.2.1,?_⟩
    rw [hclass]
    exact (properPositionRequest_eq S H f q).symm

theorem allRepresentatives_injective (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Function.Injective ((SplitAssignment.allRepresentatives r) sap nr2) := by
  intro p q he
  by_cases hp : IsRealPosition S H f p
  · by_cases hq : IsRealPosition S H f q
    · apply r.real_injective p q hp hq
      rw [(SplitAssignment.allRepresentatives_real r) sap nr2 hp,(SplitAssignment.allRepresentatives_real r) sap nr2 hq,he]
    · exact False.elim (r.real_representative_disjoint p _
        ((SplitAssignment.allRepresentatives_real r) sap nr2 hp) ⟨q,hq⟩
        (he.trans ((SplitAssignment.allRepresentatives_proper r) sap nr2 hq)))
  · by_cases hq : IsRealPosition S H f q
    · exact False.elim (r.real_representative_disjoint q _
        ((SplitAssignment.allRepresentatives_real r) sap nr2 hq) ⟨p,hp⟩
        (he.symm.trans ((SplitAssignment.allRepresentatives_proper r) sap nr2 hp)))
    · rw [(SplitAssignment.allRepresentatives_proper r) sap nr2 hp,(SplitAssignment.allRepresentatives_proper r) sap nr2 hq] at he
      exact congrArg Subtype.val (r.representatives_injective he)

theorem allRepresentatives_in_world (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (p : P) :
    (SplitAssignment.allRepresentatives r) sap nr2 p ∈ r.world.vertices := by
  by_cases hp : IsRealPosition S H f p
  · exact r.real_in_world p _ ((SplitAssignment.allRepresentatives_real r) sap nr2 hp)
  · rw [(SplitAssignment.allRepresentatives_proper r) sap nr2 hp]
    exact r.representatives_in_world ⟨p,hp⟩

end SplitAssignment

/-- The joint source13 splitting instance is applied once to this
ENTIRE finite factor. All comparisons below use its SAME output map. -/
theorem one_factor_real_representatives (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (f : CCO.UnarySupport.Structure.Hom C (originalPartialTarget S H sap nr2))
    (A : Set (Sigma X)) (hA : A.Finite) :
    ∃ r : SplitAssignment S H f.point A,
      Function.Injective ((SplitAssignment.allRepresentatives r) sap nr2) ∧
      (∀ p, RealRepresents S H ((SplitAssignment.allRepresentatives r) sap nr2 p) (r.point p)) ∧
      (∀ p, (SplitAssignment.allRepresentatives r) sap nr2 p ∈ r.world.vertices) ∧
      Nonempty (CCO.UnarySupport.Structure.Hom C (originalPartialTarget S H sap nr2)) := by
  obtain ⟨r⟩ := split_finite_assignment S H f.point sap A hA
  exact ⟨r,(SplitAssignment.allRepresentatives_injective r) sap nr2,(SplitAssignment.allRepresentatives_reads r) sap nr2,
    (SplitAssignment.allRepresentatives_in_world r) sap nr2,⟨splitAssignmentHom S H sap nr2 C f r⟩⟩

end
end CCO.GuardedTwoRoot
