import CCO.OldIdempotentForest.WordIndex
import CCO.GuardedOldSeams.LiftGraphVertices
import CCO.GuardedTwoRoot.PrivateCycleClassification

/-! The private-branch geometry of the ACTUAL shared-root word carrier.
Each branch is its original word with its canonical ordered positions.
Root and interior privacy are proved from the literal sum/sigma tags. -/

universe u v w p q
namespace CCO.OldIdempotentForest
open CCO.StrongExact CCO.GuardedTwoRoot CCO.GuardedOldSeams
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {P : Type p} {K : Type q} [Finite P] [Finite K]
namespace RootWordGeometry
variable (R : RootWordSystem S P K)

abbrev Branch := Σ k : K, Fin (R.words k).length

def branchWord (b : Branch R) : PositiveWord S (R.sort (R.left b.1)) (R.sort (R.right b.1)) :=
  (R.words b.1).get b.2

noncomputable def indexedVertex (b : Branch R)
    (p : Fin (TypedPrefix.length S (branchWord R b) + 1)) : R.Vertex :=
  R.branchPosition b.1 b.2 ((wordPositionEquiv S (branchWord R b)).symm p)

theorem indexedVertex_injective (b : Branch R) : Function.Injective (indexedVertex R b) :=
  (R.branchPosition_injective b.1 b.2).comp (wordPositionEquiv S (branchWord R b)).symm.injective

@[simp] theorem indexedVertex_first (b : Branch R) :
    indexedVertex R b 0 = Sum.inl (R.left b.1) := by
  unfold indexedVertex
  rw [← wordPositionEquiv_source S (branchWord R b),Equiv.symm_apply_apply]
  exact R.branchPosition_source b.1 b.2

@[simp] theorem indexedVertex_last (b : Branch R) :
    indexedVertex R b (Fin.last (TypedPrefix.length S (branchWord R b))) =
      Sum.inl (R.right b.1) := by
  unfold indexedVertex
  rw [← wordPositionEquiv_target S (branchWord R b),Equiv.symm_apply_apply]
  exact R.branchPosition_target b.1 b.2

theorem indexedVertex_private (b : Branch R)
    (p : Fin (TypedPrefix.length S (branchWord R b) + 1))
    (hp0 : 0 < p.val) (hpEnd : p.val < TypedPrefix.length S (branchWord R b)) :
    ∃ z : wordInterior S (branchWord R b), indexedVertex R b p = Sum.inr ⟨b.1,b.2,z⟩ := by
  let pos := (wordPositionEquiv S (branchWord R b)).symm p
  have hs : pos ≠ wordSource S (branchWord R b) := by
    intro he
    have h := congrArg (wordPositionEquiv S (branchWord R b)) he
    change wordPositionEquiv S (branchWord R b)
      ((wordPositionEquiv S (branchWord R b)).symm p) = _ at h
    rw [Equiv.apply_symm_apply,wordPositionEquiv_source] at h
    have hv := congrArg Fin.val h
    change p.val = 0 at hv
    omega
  have ht : pos ≠ wordTarget S (branchWord R b) := by
    intro he
    have h := congrArg (wordPositionEquiv S (branchWord R b)) he
    change wordPositionEquiv S (branchWord R b)
      ((wordPositionEquiv S (branchWord R b)).symm p) = _ at h
    rw [Equiv.apply_symm_apply,wordPositionEquiv_target] at h
    have hv := congrArg Fin.val h
    change p.val = TypedPrefix.length S (branchWord R b) at hv
    omega
  let z : wordInterior S (branchWord R b) := ⟨pos,hs,ht⟩
  refine ⟨z,?_⟩
  change R.embed b.1 (thetaBranchPosition S (R.words b.1) b.2 z.val) =
    R.embed b.1 (Sum.inr ⟨b.2,z⟩)
  exact congrArg (R.embed b.1) (thetaBranchPosition_interior S (R.words b.1) b.2 z)

/-- Exactly the original word steps on this actual formal carrier.
Relating this graph to the specified colour diagram is a separate lemma. -/
noncomputable def graph : SimpleGraph R.Vertex where
  Adj x y := ∃ (b : Branch R)
    (s t : Fin (TypedPrefix.length S (branchWord R b) + 1)),
    (s.val + 1 = t.val ∨ t.val + 1 = s.val) ∧
    indexedVertex R b s = x ∧ indexedVertex R b t = y
  symm := by
    constructor
    rintro x y ⟨b,s,t,hst,hs,ht⟩
    exact ⟨b,t,s,hst.elim Or.inr Or.inl,ht,hs⟩
  loopless := by
    constructor
    rintro x ⟨b,s,t,hst,hs,ht⟩
    have he := indexedVertex_injective R b (hs.trans ht.symm)
    have hv := congrArg Fin.val he
    rcases hst with hst | hst <;> omega

/-- A concrete instance, with no supplied private-path geometry or
assumed old-root witnesses. Duplicate direct descriptions remain allowed. -/
noncomputable def privateBranchSystem : PrivateBranchSystem P K (Branch R) R.Vertex where
  root := ⟨Sum.inl,fun _ _ h => Sum.inl.inj h⟩
  left := R.left
  right := R.right
  different := R.left_ne_right
  owner := Sigma.fst
  length b := TypedPrefix.length S (branchWord R b)
  positive b := TypedPrefix.length_pos S (branchWord R b)
  vertex b := ⟨indexedVertex R b,indexedVertex_injective R b⟩
  first := indexedVertex_first R
  last := indexedVertex_last R
  interior_not_root := by
    intro b p hp0 hpEnd r he
    obtain ⟨z,hz⟩ := indexedVertex_private R b p hp0 hpEnd
    change indexedVertex R b p = Sum.inl r at he
    rw [hz] at he
    cases he
  interiors_disjoint := by
    intro b c hbc p q hp0 hpEnd hq0 hqEnd he
    obtain ⟨z,hz⟩ := indexedVertex_private R b p hp0 hpEnd
    obtain ⟨z',hz'⟩ := indexedVertex_private R c q hq0 hqEnd
    change indexedVertex R b p = indexedVertex R c q at he
    rw [hz,hz'] at he
    apply hbc
    exact congrArg
      (fun t : Σ k : K, Σ b : Fin (R.words k).length, wordInterior S ((R.words k).get b) =>
        (⟨t.1,t.2.1⟩ : Branch R)) (Sum.inr.inj he)
  graph := graph R
  edge_iff _ _ := Iff.rfl

end RootWordGeometry
end CCO.OldIdempotentForest
