import PartiteConstruction.Functional.EHNStage

/-! Finite invariant bookkeeping for the ACTUAL native EHN construction.
The mathematical construction is unchanged; the concrete closed-K predicate
is discharged in RankStep. This receiving proof follows the independent
generic invariant proofs in partite-construction@f15bcdf561b8cbd488e33bf33a31874f67128d05,
without adding any upstream module to the exact105-source compatibility port. -/

namespace CCO.UnaryHN.Native.PartiteTransfer

open StructuralRamsey
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.FunctionalPartite.EHN
open Structure

universe u v

variable {L : Language.{u}}
variable {P V I : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Attach a finite list while preserving an auxiliary stage predicate.

The hypothesis `hAttach` is deliberately stated only for the concrete binary
attachment used by `Stage.attach`; all copy-retention bookkeeping is inherited
from the ordinary `attachList` proof. -/
theorem attachList_preserving
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Q : Stage K D → Prop)
    (hAttach :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding (B.induce S hS) T.system),
        Q T → Q (T.attach hK B hB hmB S hS f))
    (E : Stage K D) (hQE : Q E)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I) :
    ∃ T : Stage K D,
      Q T ∧
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        ∀ i ∈ xs,
          ∃ copy : FunctionalPartite.Embedding B T.system,
            ∀ x : S, copy x.1 = core (maps i x) := by
  induction xs with
  | nil =>
      refine ⟨E, hQE, FunctionalPartite.Embedding.id E.system, ?_⟩
      intro _ h
      exact (List.not_mem_nil h).elim
  | cons i xs ih =>
      obtain ⟨T, hQT, core, hcopies⟩ := ih
      let f := core.comp (maps i)
      let R := T.attach hK B hB hmB S hS f
      have hQR : Q R := hAttach T f hQT
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding
          B S hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding B R.system :=
        FunctionalPartite.Attachment.copyEmbedding
          B S hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, hQR, j.comp core, ?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨b, ?_⟩
        intro x
        exact FunctionalPartite.Attachment.copy_extends
          B S hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit x
      · obtain ⟨copy, hc⟩ := hcopies k hk
        exact ⟨j.comp copy, fun x => congrArg j (hc x)⟩

/-- Finite star attachment preserves every predicate preserved by the binary
attachment. -/
theorem attachAll_preserving
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Q : Stage K D → Prop)
    (hAttach :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding (B.induce S hS) T.system),
        Q T → Q (T.attach hK B hB hmB S hS f))
    (E : Stage K D) (hQE : Q E) [Finite I]
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system) :
    ∃ T : Stage K D,
      Q T ∧
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        ∀ i,
          ∃ copy : FunctionalPartite.Embedding B T.system,
            ∀ x : S, copy x.1 = core (maps i x) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨T, hQT, core, hc⟩ :=
    attachList_preserving hK B hB hmB S hS Q hAttach
      E hQE maps Finset.univ.toList
  exact ⟨T, hQT, core, fun i => hc i (by simp)⟩

end CCO.UnaryHN.Native.PartiteTransfer

