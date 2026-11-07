import CCO.GuardedOldSeams.BranchEquation
import CCO.GuardedOldSeams.LiftMenus

/-! Literal OLD branch equations in the ambient partial source. The only
embedding used is the already selected bounded joined-pair support; no
embedding or completion of the whole source is assumed. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.StrongExact
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (k : GuardedPair S H sap nr2 F)

def guardedPairReadLeft :
    (originalCompletedStructure S H sap nr2).Carrier (F.sort k.val.1) :=
  let e := guardedPairEmbedding S H sap nr2 F hUnary tests k
  let b := guardedPairLeft S H sap nr2 F k
  ⟨e.point b,e.sort_eq b⟩

def guardedPairReadRight :
    (originalCompletedStructure S H sap nr2).Carrier (F.sort k.val.2) :=
  let e := guardedPairEmbedding S H sap nr2 F hUnary tests k
  let c := guardedPairRight S H sap nr2 F k
  ⟨e.point c,e.sort_eq c⟩

variable (J : OriginalNamedHiddenCoordinate S H (F.sort k.val.1).down.1)
variable (p : PositiveWord S (F.sort k.val.1).down.1 (F.sort k.val.2).down.1)
variable (hKernel : ∀ x z : X (F.sort k.val.1).down.1,
  (∃ y : X (F.sort k.val.2).down.1,
    S.menuRel (PositiveWord.profile S p) x y ∧
    S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
variable (hContains : guardedPairMenu S H sap nr2 F hUnary tests k ⊆
  PositiveWord.profile S p)

/-- The literal source equation is reflected on the SAME selected local
factor and then included back into the unchanged ambient OLD vertices. -/
theorem guarded_old_branch_equation :
    ∃ hMenu : (guardedPairMenu S H sap nr2 F hUnary tests k).Nonempty,
      LiteralOldEquation S H sap nr2 F
        (branchLeftTerm S H sap nr2
          (guardedPairReadLeft S H sap nr2 F hUnary tests k)
          (guardedPairReadRight S H sap nr2 F hUnary tests k)
          hMenu J p hKernel hContains)
        (branchRightTerm S H sap nr2
          (guardedPairReadLeft S H sap nr2 F hUnary tests k)
          (guardedPairReadRight S H sap nr2 F hUnary tests k)
          hMenu J p hKernel hContains) k.val.1 k.val.2 := by
  obtain ⟨hMenu,hEq⟩ := old_branch_equation S H sap nr2
    (F.closureStructure {k.val.1,k.val.2})
    (guardedPairEmbedding S H sap nr2 F hUnary tests k)
    (guardedPairLeft S H sap nr2 F k) (guardedPairRight S H sap nr2 F k)
    (fun he => k.property.1 (congrArg Subtype.val he)) J p hKernel hContains
  exact ⟨hMenu,LiteralOldEquation.of_closed_support S H sap nr2
    (F.isClosed_closure {k.val.1,k.val.2}) hEq⟩

/-- The atomic representative and its actual named transition have the
same ambient OLD equation, with the common atom derived on that support. -/
theorem guarded_old_branch_atomic_equation :
    ∃ (a : S.Atom (F.sort k.val.1).down.1 (F.sort k.val.2).down.1)
      (ha : a ∈ guardedPairMenu S H sap nr2 F hUnary tests k)
      (hMenu : (guardedPairMenu S H sap nr2 F hUnary tests k).Nonempty),
      LiteralOldEquation S H sap nr2 F
        (branchAtomicLeftTerm S H sap nr2
          (guardedPairReadLeft S H sap nr2 F hUnary tests k)
          (guardedPairReadRight S H sap nr2 F hUnary tests k)
          hMenu J p hKernel hContains a (hContains ha))
        (branchAtomicRightTerm S H sap nr2
          (guardedPairReadLeft S H sap nr2 F hUnary tests k)
          (guardedPairReadRight S H sap nr2 F hUnary tests k)
          hMenu J p hKernel hContains a (hContains ha)) k.val.1 k.val.2 := by
  obtain ⟨a,ha,hMenu,hEq⟩ := old_branch_atomic_equation S H sap nr2
    (F.closureStructure {k.val.1,k.val.2})
    (guardedPairEmbedding S H sap nr2 F hUnary tests k)
    (guardedPairLeft S H sap nr2 F k) (guardedPairRight S H sap nr2 F k)
    (fun he => k.property.1 (congrArg Subtype.val he)) J p hKernel hContains
  exact ⟨a,ha,hMenu,LiteralOldEquation.of_closed_support S H sap nr2
    (F.isClosed_closure {k.val.1,k.val.2}) hEq⟩

end
end CCO.GuardedOldSeams
