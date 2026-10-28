import CCO.FiniteHelpers
import Mathlib.Data.Finset.Union

/-!
# A disjoint real copy over a prescribed pointwise base

This is only the preliminary SAP copy. No selected independence, selector,
CCO or orbit-infinitude hypothesis occurs. Both embeddings of an actual SAP
amalgam extend by finite homogeneity; their relative automorphism aligns the
whole fixed right side and retains the literal overlap supplied by SAP.
-/

universe u v w t

namespace CCO.SIR.Positive

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [MulAction G (Sigma X)]
variable [DecidableEq (Sigma X)]

/-- Move `A` by a single original automorphism fixing `C` pointwise, so its
intersection with the actual prescribed `B` is contained in `C`. Empty sides,
empty bases and arbitrary old overlaps are included.
-/
theorem disjoint_copy_over (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A B C : Finset (Sigma X)) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧
      ∀ a ∈ A, ∀ b ∈ B, g • a = b → b ∈ C := by
  classical
  let AC := FiniteInduced.ofFinset (A ∪ C)
  let BC := FiniteInduced.ofFinset (B ∪ C)
  let CC := FiniteInduced.ofFinset C
  let incA : InducedEmbedding S CC AC := inducedInclusion S CC AC
    (fun _ hc => Finset.mem_union_right A hc)
  let incB : InducedEmbedding S CC BC := inducedInclusion S CC BC
    (fun _ hc => Finset.mem_union_right B hc)
  obtain ⟨D, eA, eB, hcomm, hinter⟩ := sap.strong_amalgamate CC AC BC incA incB
  obtain ⟨ga, hga⟩ := H.extends_partial_iso AC D eA
  obtain ⟨gb, hgb⟩ := H.extends_partial_iso BC D eB
  have halign (c : ↥CC.vertices) : ga • c.val = gb • c.val := by
    have hc := congrArg Subtype.val (hcomm c)
    exact (hga (incA.toEmbedding c)).trans
      (hc.trans (hgb (incB.toEmbedding c)).symm)
  refine ⟨gb⁻¹ * ga, ?_, ?_⟩
  · intro c hc
    rw [mul_smul]
    rw [halign ⟨c, hc⟩, inv_smul_smul]
  · intro a ha b hb hab
    let a' : ↥AC.vertices := ⟨a, Finset.mem_union_left C ha⟩
    let b' : ↥BC.vertices := ⟨b, Finset.mem_union_left C hb⟩
    have hp : ga • a = gb • b := by
      have hh := congrArg (fun p : Sigma X => gb • p) hab
      simpa only [mul_smul, smul_inv_smul] using hh
    have heq : eA.toEmbedding a' = eB.toEmbedding b' := by
      apply Subtype.ext
      exact (hga a').symm.trans (hp.trans (hgb b'))
    obtain ⟨c, _, hcb⟩ := hinter a' b' heq
    have hval : c.val = b := congrArg Subtype.val hcb
    exact hval ▸ c.property

end CCO.SIR.Positive
