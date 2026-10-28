import CCO.StrongExact.ThetaPairLineMap
import CCO.StrongExact.ThetaCycleTwoLiteralLines
import CCO.StrongExact.ThetaCycleFirstArcLetters
import CCO.StrongExact.ThetaCycleRightArcLetters
import CCO.StrongExact.ThetaCycleTwoArcIndexCover
import CCO.StrongExact.ThetaCycleCompatibility
import Lean.Elab.Tactic.Omega

/-!
# Every actual hard-theta cycle has an original-colour homomorphism

The two genuine simple-cycle arcs are complete original words with
intersecting strong profiles. Their literal real line witnesses have the
same two endpoints. Glue those two lines and use the half-open arc cover
to preserve every specified cyclic edge, reversing the second word with
the original source converse. CCO is not needed for this cycle witness.
-/

universe u v w
namespace CCO.StrongExact

private theorem thetaCycle_two_arc_step_cover
    {n : Nat} (hn : 0 < n) (p q : Fin n) (k l : Nat)
    (hForward : thetaCycleAdvance hn p k = q)
    (hSum : k + l = n) (r : Fin n) :
    (∃ m : Nat, m < k ∧ thetaCycleAdvance hn p m = r) ∨
    (∃ t : Nat, t < l ∧ thetaCycleAdvance hn q t = r) := by
  obtain ⟨m,hm,hReached⟩ := thetaCycleAdvance_reaches hn p r
  by_cases hSmall : m < k
  · exact Or.inl ⟨m,hSmall,hReached⟩
  · let t : Nat := m - k
    have ht : t < l := by
      dsimp only [t]
      omega
    right
    refine ⟨t,ht,?_⟩
    calc
      thetaCycleAdvance hn q t =
          thetaCycleAdvance hn (thetaCycleAdvance hn p k) t := by rw [hForward]
      _ = thetaCycleAdvance hn p (k + t) :=
          (thetaCycleAdvance_add hn p k t).symm
      _ = thetaCycleAdvance hn p m := by rw [show k + t = m by omega]
      _ = r := hReached

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Every specified simple cycle in the actual long-word theta has a
homomorphism into the ORIGINAL source under homogeneous SAP. This is
an actual `CycleHom` witness, not a conditional provider premise. -/
theorem thetaCycleHom_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (hPair : PairwiseWordProfiles S ws)
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    CycleHom C := by
  classical
  obtain ⟨p,q,k,l,b,c,hDistinct,hKpos,hKlt,hForward,hLlt,
      hBackward,hLeft,hRight,hArcB,hArcC,hLines⟩ :=
    thetaCycle_two_literal_lines_of_SAP S H sap ws hPair hLong C
  obtain ⟨a,x,y,lineB,lineC,_hxy⟩ := hLines
  let point := thetaPairLinePoint S ws b c x y lineB lineC
  have hB : ∀ e : wordEdgeIndex S (ws.get b),
      ThetaPairPreserves S ((thetaEdgesOfLong S ws hLong).toDiagram)
        point (thetaBranchEdgeSource S ws b e)
        (thetaBranchEdgeTarget S ws b e) := by
    intro e
    exact thetaPairPreserves_of_literalLine S ws hLong point b x y lineB
      (thetaPairLinePoint_first_image S ws b c x y lineB lineC) e
  have hC : ∀ e : wordEdgeIndex S (ws.get c),
      ThetaPairPreserves S ((thetaEdgesOfLong S ws hLong).toDiagram)
        point (thetaBranchEdgeSource S ws c e)
        (thetaBranchEdgeTarget S ws c e) := by
    intro e
    exact thetaPairPreserves_of_literalLine S ws hLong point c x y lineC
      (thetaPairLinePoint_second_image S ws b c hDistinct x y lineB lineC) e
  have hLtwo := thetaCycle_right_left_distance_ge_two
    S ws hLong C q p l hRight hLeft hBackward
  have hLpos : 0 < l := by omega
  have hSum := thetaCycle_two_arc_lengths_add C.length_pos
    p q k l hKpos hLpos hKlt hLlt hForward hBackward
  refine ⟨fun r => point (C.vertices r), ?_⟩
  intro r a ha
  have hStep :
      ThetaPairPreserves S ((thetaEdgesOfLong S ws hLong).toDiagram)
        point (C.vertices r) (C.vertices (cyclicNext C.length_pos r)) := by
    rcases thetaCycle_two_arc_step_cover C.length_pos p q k l
        hForward hSum r with ⟨m,hm,hr⟩ | ⟨m,hm,hr⟩
    · obtain ⟨e,hs,ht⟩ := thetaCycle_left_arc_step_is_letter
        S ws hLong C p q k hLeft hRight hKlt hForward b hArcB m hm
      have hSource : C.vertices r = thetaBranchEdgeSource S ws b e := by
        rw [← hr]
        exact hs
      have hTarget : C.vertices (cyclicNext C.length_pos r) =
          thetaBranchEdgeTarget S ws b e := by
        rw [← hr]
        exact ht
      rw [hSource,hTarget]
      exact hB e
    · obtain ⟨e,ht,hs⟩ := thetaCycle_right_arc_step_is_reverse_letter
        S ws hLong C q p l hRight hLeft hLlt hBackward c hArcC m hm
      have hTarget : C.vertices r = thetaBranchEdgeTarget S ws c e := by
        rw [← hr]
        exact ht
      have hSource : C.vertices (cyclicNext C.length_pos r) =
          thetaBranchEdgeSource S ws c e := by
        rw [← hr]
        exact hs
      rw [hTarget,hSource]
      exact thetaPairPreserves_reverse S
        ((thetaEdgesOfLong S ws hLong).toDiagram) point (hC e)
  exact hStep (C.next_ne r) a ha

/-- Discharge the original explicit cycle compatibility seam from
homogeneous SAP, without requiring CCO to manufacture a cycle witness. -/
theorem thetaCycleCompatibility_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) :
    ThetaCycleCompatibility S := by
  intro i j ws hPair _hLength hLong C
  exact thetaCycleHom_of_SAP S H sap ws hPair hLong C

/-- The constructed old-colour theta edges and proved actual cycle
homomorphisms discharge the original hard theta provider. -/
theorem hardThetaProvider_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) :
    HardThetaProvider S :=
  hardThetaProvider_of_cycleCompatibility S
    (thetaCycleCompatibility_of_SAP S H sap)

/-- Positive STRONG word 2-Helly over the original homogeneous SAP+CCO
source, including empty, small and direct-letter families through the
already proved reductions. No theta/Helly provider remains a hypothesis. -/
theorem wordHelly_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) : WordHelly S :=
  wordHelly_of_hardThetaProvider S H sap cco
    (hardThetaProvider_of_SAP S H sap)

end CCO.StrongExact
