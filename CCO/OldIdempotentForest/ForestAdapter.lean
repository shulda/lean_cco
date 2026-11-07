import CCO.OldIdempotentForest.MacroIntervals
import CCO.FactorizationForest.Provider

/-!
# The received forest theorem on the actual typed macro occurrence word

The alphabet consists of the original occurrence indices `Fin n`.  The
yield is literally `List.finRange n`, so neither repeated branch words
nor equal positive profiles can replace an occurrence.  The semigroup
is the actual positive reachable-profile semigroup with its absorbing
mismatch zero; no STRONG identity is adjoined.
-/

universe u v w r

namespace CCO.OldIdempotentForest

noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

namespace MacroPath

variable {S} {n : ℕ} (P : MacroPath S n)

/-- C05, with the provider's sharper height bound and its exact original
ordered occurrence yield. The only forest existence input is the proved
receiving theorem, instantiated on the actual typed source semigroup. -/
theorem exists_factorization_forest_sharp (hn : 0 < n) :
    letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
    ∃ t : FactorizationTree (Fin n),
      t.value = List.finRange n ∧ t.IsRamsey (P.eval H sap) ∧
        t.height ≤ 3 * Nat.card (TypedProfileState S) - 1 := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  have hword : List.finRange n ≠ [] :=
    List.length_pos_iff.mp (by simpa only [List.length_finRange] using hn)
  have hmul : ∀ left right : List (Fin n), left ≠ [] → right ≠ [] →
      P.eval H sap (left ++ right) = P.eval H sap left * P.eval H sap right := by
    intro left right hl hr
    exact P.eval_append H sap left right hl hr
  obtain ⟨t, hvalue, hramsey, hheight⟩ := CCO.FactorizationForest.classical_bound
    (P.eval H sap) hmul (List.finRange n) hword
  refine ⟨t, hvalue, hramsey, ?_⟩
  simpa only [Nat.card_eq_fintype_card] using hheight

/-- The source's stipulated `h = 3 |S_typ|` follows from the stronger
received bound without changing the semigroup or its cardinality. -/
theorem exists_factorization_forest (hn : 0 < n) :
    letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
    ∃ t : FactorizationTree (Fin n),
      t.value = List.finRange n ∧ t.IsRamsey (P.eval H sap) ∧
        t.height ≤ 3 * Nat.card (TypedProfileState S) := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  obtain ⟨t, hvalue, hramsey, hheight⟩ := P.exists_factorization_forest_sharp H sap hn
  exact ⟨t, hvalue, hramsey, hheight.trans (Nat.sub_le _ _)⟩

/-- Data retained by the ordered-interval and stopped-pruning consumers.
The Ramsey predicate uses precisely the original-source multiplication. -/
structure Forest where
  tree : FactorizationTree (Fin n)
  original_yield : tree.value = List.finRange n
  ramsey : letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
    tree.IsRamsey (P.eval H sap)
  height_bound : tree.height ≤ 3 * Nat.card (TypedProfileState S)

theorem forest_exists (hn : 0 < n) : Nonempty (P.Forest H sap) := by
  obtain ⟨t, hyield, hramsey, hheight⟩ := P.exists_factorization_forest H sap hn
  exact ⟨⟨t, hyield, hramsey, hheight⟩⟩

end MacroPath
end
end CCO.OldIdempotentForest
