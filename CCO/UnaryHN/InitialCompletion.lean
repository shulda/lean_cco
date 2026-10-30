import CCO.UnaryHN.ClosedAmalgam
import CCO.UnaryHN.AdmissibleClass
import PartiteConstruction.Functional.EHNInitial

/-! Actual K-completion of the native finite initial B-picture. Empty
overlaps retain B's nullary diagram by the existing full root embedding. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {K : Class.{u,v} L}

theorem empty_irreducible {H : Type v} [IsEmpty H] (Root : Structure L H) :
    Root.Irreducible := by
  intro G E F C Common Left Right Whole sL sR iL iR hFree e
  exact Or.inl (fun x => isEmptyElim x)

theorem completion_glue_irreducible_root (hK : FiniteHereditarySAP K)
    {H E F C : Type v} {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (hRoot : Root.Irreducible)
    (hL : HasCompletion K Left) (hR : HasCompletion K Right) :
    HasCompletion K Whole := by
  obtain ⟨XL, hXL, TL, hTL, qL, hqL⟩ := hL
  obtain ⟨XR, hXR, TR, hTR, qR, hqR⟩ := hR
  obtain ⟨eL, heL⟩ := hqL.2 Root hRoot sL
  obtain ⟨eR, heR⟩ := hqR.2 Root hRoot sR
  obtain ⟨X, hX, Target, hT, jL, jR, hAgree, _⟩ := hK.strong hTL hTR eL eR
  have hCompat : ∀ z, (jL ∘ qL) (sL z) = (jR ∘ qR) (sR z) := by
    intro z
    exact (congrArg jL (heL z).symm).trans
      ((hAgree z).trans (congrArg jR (heR z)))
  obtain ⟨p, hp, _, _⟩ := free_completion_glue hFree (jL ∘ qL) (jR ∘ qR)
    (jL.isEHNHomomorphismEmbedding.comp hqL)
    (jR.isEHNHomomorphismEmbedding.comp hqR) hCompat
  exact ⟨X, hX, Target, hT, p, hp⟩

namespace PartiteTransfer

open StructuralRamsey.FunctionalPartite
open StructuralRamsey.FunctionalPartite.EHN

variable {P V : Type v} {D : Structure L P}

theorem initial_completable_list (hK : FiniteHereditarySAP K)
    (B : Structure L V) [Finite V] (hB : K B) (hPos : L.PositiveFuncArity)
    (beta0 : Embedding B D) (xs : List (Embedding B D)) :
    ∃ T : Stage (admissibleClass K) D,
      HasCompletion K T.system.toStructure ∧
      ∃ _ : Embedding B T.system.toStructure,
        ∀ beta ∈ xs, ∃ e : Embedding B T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  let hJ := admissibleClass_free K
  have hJB : admissibleClass K B := admissibleClass_of_mem hK hB
  induction xs with
  | nil =>
      let T : Stage (admissibleClass K) D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed B beta0
        isPartite := placed_over B beta0
        mem := hJB
      }
      exact ⟨T, HasCompletion.of_mem hK hB, Embedding.id B,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons beta xs ih =>
      obtain ⟨T, hT, root, hCopies⟩ := ih
      let Q := placed B beta
      have hS : Q.toStructure.IsClosed ∅ := empty_closed B hPos
      let f : FunctionalPartite.Embedding (Q.induce ∅ hS) T.system := {
        toEmbedding := root.comp (inclusion B ∅ hS)
        map_part := fun x => x.2.elim
      }
      let R := T.attach hJ Q (placed_over B beta) hJB ∅ hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding Q ∅ hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding Q ∅ hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit
      have hComp : HasCompletion K R.system.toStructure :=
        completion_glue_irreducible_root hK
          (Structure.Attachment.unit_isFreeAmalgam B ∅ hS T.system.toStructure f.toEmbedding)
          (empty_irreducible (B.induce ∅ hS)) hT (HasCompletion.of_mem hK hB)
      refine ⟨R, hComp, j.toEmbedding.comp root, ?_⟩
      intro gamma hGamma
      rcases List.mem_cons.mp hGamma with rfl | hGamma
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hCopies gamma hGamma
        exact ⟨j.toEmbedding.comp e, fun x => (j.map_part (e x)).trans (he x)⟩

theorem initial_completable (hK : FiniteHereditarySAP K)
    (B : Structure L V) [Finite V] [Finite P] (hB : K B)
    (hPos : L.PositiveFuncArity) (beta0 : Embedding B D) :
    ∃ T : Stage (admissibleClass K) D,
      HasCompletion K T.system.toStructure ∧
      ∀ beta : Embedding B D, ∃ e : Embedding B T.system.toStructure,
        ∀ x, T.system.part (e x) = beta x := by
  classical
  let : Fintype (Embedding B D) := Fintype.ofFinite _
  obtain ⟨T, hT, _, hCopies⟩ :=
    initial_completable_list hK B hB hPos beta0 Finset.univ.toList
  exact ⟨T, hT, fun beta => hCopies beta (by simp)⟩

end PartiteTransfer
end CCO.UnaryHN.Native
