import CCO.UnaryHN.MixedCompletion
import CCO.UnaryHN.InitialCompletion
import CCO.UnaryHN.PictureInvariant
import CCO.UnaryHN.RamseyInvariant

/-! One ACTUAL native Hales--Jewett/Picture pass raises the ordinary
closed K-completion bound.  Pure tests use the constructed stage invariant;
mixed tests use only the predecessor control at one smaller cardinality. -/

universe u v w
namespace CCO.UnaryHN.Native.PartiteTransfer

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.FunctionalPartite.EHN

variable {L : Language.{u}} {K : Class.{u,v} L} {U P : Type v}
variable {A : Structure L U} {D : Structure L P}

theorem attach_closed_rank (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) (hA : K A) (alpha : Structure.Embedding A D)
    (m : ℕ) (hPrev : ClosedSmallCompletable K D m)
    (Old T : Stage (admissibleClass K) D)
    (f : FunctionalPartite.Embedding
      (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
        (Old.system.weak_support_closed D Old.isPartite.1 A alpha)) T.system)
    (hOld : ClosedSmallCompletable K Old.system.toStructure (m + 1))
    (hT : ClosedSmallCompletable K T.system.toStructure (m + 1)) :
    ClosedSmallCompletable K
      (T.attach (admissibleClass_free K) Old.system Old.isPartite Old.mem
        (Old.system.support alpha.toFunctionEmbedding)
        (Old.system.weak_support_closed D Old.isPartite.1 A alpha) f).system.toStructure
      (m + 1) := by
  classical
  let Supp := Old.system.support alpha.toFunctionEmbedding
  have hSupp := Old.system.weak_support_closed D Old.isPartite.1 A alpha
  let R := T.attach (admissibleClass_free K) Old.system Old.isPartite Old.mem Supp hSupp f
  let Whole := R.system.toStructure
  let iCore : Structure.Embedding T.system.toStructure Whole :=
    Structure.Attachment.coreEmbedding Old.system.toStructure Supp hSupp T.system.toStructure
      (fun _ : PUnit.{v+1} => f.toEmbedding)
  let iCopy : Structure.Embedding Old.system.toStructure Whole :=
    Structure.Attachment.copyEmbedding Old.system.toStructure Supp hSupp T.system.toStructure
      (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit
  have hFree := Structure.Attachment.unit_isFreeAmalgam
    Old.system.toStructure Supp hSupp T.system.toStructure f.toEmbedding
  intro S hSize hClosed
  have hCard : Nat.card (↑S : Set R.Carrier) ≤ m + 1 := by
    have hc : Fintype.card (↑S : Set R.Carrier) = S.card :=
      Fintype.card_of_finset' S (fun _ => Iff.rfl)
    rwa [Nat.card_eq_fintype_card, hc]
  let inc : Structure.Embedding (Whole.induce (↑S : Set R.Carrier) hClosed) Whole :=
    inclusion Whole (↑S : Set R.Carrier) hClosed
  by_cases hCore : ∀ x : (↑S : Set R.Carrier), ∃ y, x.val = iCore y
  · let e := inc.factorThroughClosedRange iCore hCore
    exact hT.completion_of_embedding e hCard
  · by_cases hCopy : ∀ x : (↑S : Set R.Carrier), ∃ y, x.val = iCopy y
    · let e := inc.factorThroughClosedRange iCopy hCopy
      exact hOld.completion_of_embedding e hCard
    · have hOutsideCore : ∃ z ∈ S, ∀ y, z ≠ iCore y := by
        obtain ⟨x, hx⟩ := not_forall.mp hCore
        exact ⟨x.val, x.2, fun y hy => hx ⟨y, hy⟩⟩
      have hOutsideCopy : ∃ z ∈ S, ∀ y, z ≠ iCopy y := by
        obtain ⟨x, hx⟩ := not_forall.mp hCopy
        exact ⟨x.val, x.2, fun y hy => hx ⟨y, hy⟩⟩
      have hRoot : ∀ z : Supp, ∃ a, R.system.part (iCore (f z)) = alpha a := by
        intro z
        obtain ⟨a, ha⟩ := z.2
        exact ⟨a, (f.map_part z).trans ha.symm⟩
      exact mixed_closed_completion hK hIrr hUnary hFree D alpha hA
        R.system.part R.isPartite hRoot m hPrev S hSize hClosed hOutsideCore hOutsideCopy

theorem picture_closed_rank (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) [Finite U] (hA : K A)
    (m : ℕ) (hPrev : ClosedSmallCompletable K D m)
    (Old : Stage (admissibleClass K) D)
    (hOld : ClosedSmallCompletable K Old.system.toStructure (m + 1))
    (alpha : Structure.Embedding A D) (κ : Type w) [Fintype κ] :
    ∃ T : Stage (admissibleClass K) D,
      ClosedSmallCompletable K T.system.toStructure (m + 1) ∧
      PictureProperty A Old T alpha κ := by
  let Q : Stage (admissibleClass K) D → Prop := fun T =>
    ClosedSmallCompletable K T.system.toStructure (m + 1)
  apply pictureLemma_preservingSupport (admissibleClass_free K) A
    (admissibleClass_of_mem hK hA) Old alpha κ Q
  · intro N hN
    let B := Old.system.weakRestrict D Old.isPartite.1 A alpha
    have hB : B.WeaklyPartiteOver A :=
      Old.system.weakRestrict_invariant D Old.isPartite.1 A alpha Old.isPartite
    have hPower : (Induced.power B N).WeaklyPartiteOver A :=
      Induced.power_weaklyPartiteOver hB hN
    have hComp : HasCompletion K (Induced.power B N).toStructure :=
      HasCompletion.pullback hPower (HasCompletion.of_mem hK hA)
    exact closed_small_of_completion hComp (m + 1)
  · intro T f hT
    exact attach_closed_rank hK hIrr hUnary hA alpha m hPrev Old T f hOld hT

theorem closed_rank_pass (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) (A : Structure L U) {V : Type v} (B : Structure L V)
    [Finite U] [Finite V] [Finite P] (hA : K A) (hB : K B)
    (κ : Type w) [Fintype κ] [Nonempty κ] (hArrow : Structure.Arrow A B D κ)
    (m : ℕ) (hPrev : ClosedSmallCompletable K D m) :
    ∃ T : Stage (admissibleClass K) D,
      ClosedSmallCompletable K T.system.toStructure (m + 1) ∧
      Structure.Arrow A B T.system.toStructure κ := by
  have hPos : L.PositiveFuncArity := by intro F; rw [hUnary F]; decide
  let Q : Stage (admissibleClass K) D → Prop := fun T =>
    ClosedSmallCompletable K T.system.toStructure (m + 1)
  apply inducedConstruction_preserving A B D κ hArrow Q
  · intro beta0
    obtain ⟨T, hT, hCopies⟩ := initial_completable hK B hB hPos beta0
    exact ⟨T, closed_small_of_completion hT (m + 1), hCopies⟩
  · intro Old alpha hOld
    exact picture_closed_rank hK hIrr hUnary hA m hPrev Old hOld alpha κ

end CCO.UnaryHN.Native.PartiteTransfer
