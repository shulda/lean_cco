import CCO.StrongExact.ThetaCompatibleLines
import CCO.StrongExact.ThetaCycleTwoArcDistinct

/-!
# C07: compatible literal real word lines for the ACTUAL two cycle branches

A genuine hard-theta specified cycle has two distinct word-occurrence
tags on its two complete root-to-root arcs. Their positive strong
profiles intersect by the original pairwise C07 premise. Under
original homogeneous SAP, those TWO words therefore have literal
old-atom walk witnesses with precisely the SAME actual real endpoints.
This is the concrete source of the later CycleHom point assignment.
It does NOT yet assert that such an assignment has been constructed.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- The two actual theta-cycle branches admit source-realized literal
word lines with common real roots and correct original fine atoms.
Their precise cyclic supports are included in the conclusion, rather
than merely finding two unrelated compatible profiles in the list. -/
theorem thetaCycle_two_literal_lines_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (hPair : PairwiseWordProfiles S ws)
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p q : Fin C.length, ∃ k l : Nat,
      ∃ b c : Fin ws.length,
        b ≠ c ∧ 0 < k ∧ k < C.length ∧
        thetaCycleAdvance C.length_pos p k = q ∧
        l < C.length ∧
        thetaCycleAdvance C.length_pos q l = p ∧
        C.vertices p = thetaLeft S ws ∧
        C.vertices q = thetaRight S ws ∧
        (∀ m : Nat, 0 < m → m < k →
          ∃ t : wordInterior S (ws.get b),
            C.vertices (thetaCycleAdvance C.length_pos p m) =
              (.inr ⟨b,t⟩ : thetaVertices S ws)) ∧
        (∀ m : Nat, 0 < m → m < l →
          ∃ t : wordInterior S (ws.get c),
            C.vertices (thetaCycleAdvance C.length_pos q m) =
              (.inr ⟨c,t⟩ : thetaVertices S ws)) ∧
        (∃ (a : S.Atom i j) (x : X i) (y : X j),
          ∃ (lineB : LiteralLine S (ws.get b) x y)
            (lineC : LiteralLine S (ws.get c) x y),
            S.colour x y = some a) := by
  obtain ⟨p,q,k,l,b,c,hDistinct,hKpos,hKlt,hForward,hLlt,hBackward,
      hLeft,hRight,hArcB,hArcC⟩ :=
    thetaCycle_two_arcs_distinct_branch_tags S ws hLong C
  have hInter :
      (PositiveWord.profile S (ws.get b) ∩
        PositiveWord.profile S (ws.get c)).Nonempty :=
    hPair (ws.get b) (List.get_mem ws b)
      (ws.get c) (List.get_mem ws c)
  obtain ⟨a,x,y,lineB,lineC,hxy⟩ :=
    two_literal_lines_of_intersecting_profiles S H sap
      (ws.get b) (ws.get c) hInter
  exact ⟨p,q,k,l,b,c,hDistinct,hKpos,hKlt,hForward,hLlt,
    hBackward,hLeft,hRight,hArcB,hArcC,
    a,x,y,lineB,lineC,hxy⟩

end CCO.StrongExact
