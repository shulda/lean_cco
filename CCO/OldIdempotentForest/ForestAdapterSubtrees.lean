import CCO.OldIdempotentForest.ForestAdapterComposable

/-! Every received subtree is a positive ORIGINAL contiguous interval.
Consequently a common child idempotent is nonzero and is an actual
same-sort strong reachable diversity profile.  These deductions use the
received ordered tree and actual composability, with no pruning premise. -/

universe u v w r a b

namespace CCO.OldIdempotentForest

/-- A literal node of the supplied ordered tree, including the root. -/
inductive ForestSubtree {A : Type a} : FactorizationTree A → FactorizationTree A → Prop
  | refl (t) : ForestSubtree t t
  | binary_left (l r) {t} (h : ForestSubtree t l) : ForestSubtree t (.binary l r)
  | binary_right (l r) {t} (h : ForestSubtree t r) : ForestSubtree t (.binary l r)
  | idempotent_child (children) (c) (hc : c ∈ children) {t}
      (h : ForestSubtree t c) : ForestSubtree t (.idempotent children)

namespace ForestSubtree

variable {A : Type a}

theorem trans {s t root : FactorizationTree A}
    (hst : ForestSubtree s t) (htr : ForestSubtree t root) : ForestSubtree s root := by
  induction htr with
  | refl t => exact hst
  | binary_left l r h ih => exact .binary_left l r (ih hst)
  | binary_right l r h ih => exact .binary_right l r (ih hst)
  | idempotent_child children c hc h ih => exact .idempotent_child children c hc (ih hst)

private theorem child_value_infix_listValue (children : List (FactorizationTree A))
    (c : FactorizationTree A) (hc : c ∈ children) :
    c.value <:+: FactorizationTree.listValue children := by
  induction children with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.infix_append_left
      · exact List.infix_append_of_infix_right (ih hc)

/-- Child order and original yields give actual contiguous subwords,
not merely subsets of letters or another equal semigroup product. -/
theorem value_infix {t root : FactorizationTree A} (h : ForestSubtree t root) :
    t.value <:+: root.value := by
  induction h with
  | refl t => exact List.infix_rfl
  | binary_left l r h ih => exact List.infix_append_of_infix_left ih
  | binary_right l r h ih => exact List.infix_append_of_infix_right ih
  | idempotent_child children c hc h ih =>
      exact ih.trans (child_value_infix_listValue children c hc)

/-- Ramsey validity is inherited by every literal supplied subtree. -/
theorem ramsey {T : Type b} [Semigroup T] (eval : List A → T)
    {t root : FactorizationTree A} (h : ForestSubtree t root) :
    root.IsRamsey eval → t.IsRamsey eval := by
  induction h with
  | refl t => exact fun ht => ht
  | binary_left l r h ih =>
      exact fun ht => ih ((FactorizationTree.isRamsey_binary eval l r).mp ht).1
  | binary_right l r h ih =>
      exact fun ht => ih ((FactorizationTree.isRamsey_binary eval l r).mp ht).2
  | idempotent_child children c hc h ih =>
      intro ht
      have hn := (FactorizationTree.isRamsey_idempotent eval children).mp ht
      exact ih ((FactorizationTree.listIsRamsey_iff eval children).mp hn.2.1 c hc)

theorem height_le {t root : FactorizationTree A} (h : ForestSubtree t root) :
    t.height ≤ root.height := by
  induction h with
  | refl t => exact le_refl _
  | binary_left l r h ih =>
      exact ih.trans (Nat.le_of_succ_le (FactorizationTree.height_ge_child_of_binary_left l r))
  | binary_right l r h ih =>
      exact ih.trans (Nat.le_of_succ_le (FactorizationTree.height_ge_child_of_binary_right l r))
  | idempotent_child children c hc h ih =>
      exact ih.trans (Nat.le_of_succ_le (FactorizationTree.height_ge_child_of_idempotent hc))

end ForestSubtree

noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- C06 for the indexed composable-list adapter: every actual forest
node is a nonempty original interval and hence cannot be the adjoined zero. -/
theorem composable_forest_subtree_nonzero
    (letters : List (ReachableProfile S))
    (hcomp : letters.IsChain ReachableProfile.Compatible)
    (root t : FactorizationTree (Fin letters.length))
    (hyield : root.value = List.finRange letters.length)
    (hramsey : letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
      root.IsRamsey (indexedProfileEval S H sap letters))
    (hsub : ForestSubtree t root) :
    indexedProfileEval S H sap letters t.value ≠ .zero := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  have ht := ForestSubtree.ramsey (indexedProfileEval S H sap letters) hsub hramsey
  have hne := FactorizationTree.tree_value_ne_nil t ht
  have hinfix := hsub.value_infix
  rw [hyield] at hinfix
  exact indexedProfileEval_infix_nonzero S H sap letters hcomp t.value hne hinfix

/-- Every common idempotent at a valid received idempotent node is an
actual nonempty reachable same-sort strong profile.  This also covers
binary idempotent nodes; the pruner separately keeps both their children. -/
theorem composable_forest_common_child_profile
    (letters : List (ReachableProfile S))
    (hcomp : letters.IsChain ReachableProfile.Compatible)
    (root : FactorizationTree (Fin letters.length))
    (hyield : root.value = List.finRange letters.length)
    (hramsey : letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
      root.IsRamsey (indexedProfileEval S H sap letters))
    (children : List (FactorizationTree (Fin letters.length)))
    (hsub : ForestSubtree (.idempotent children) root) :
    ∃ (i : ι) (P : S.Menu i i) (hP : P.Nonempty)
      (hReach : ∃ word : PositiveWord S i i, PositiveWord.profile S word = P),
      S.product P P = P ∧
      ∀ c ∈ children, indexedProfileEval S H sap letters c.value =
        .positive ⟨⟨i,i,⟨P,hP⟩⟩,hReach⟩ := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  have hnode := ForestSubtree.ramsey (indexedProfileEval S H sap letters) hsub hramsey
  obtain ⟨hlen, _, e, he, hvalues⟩ :=
    (FactorizationTree.isRamsey_idempotent (indexedProfileEval S H sap letters) children).mp hnode
  have hchildren : children ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    exact (by decide : ¬ 2 ≤ 0) hlen
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil children hchildren
  have hcsub : ForestSubtree c root := by
    have hchild : ForestSubtree c (.idempotent children) :=
      .idempotent_child children c hc (.refl c)
    exact hchild.trans hsub
  have henonzero : e ≠ .zero := by
    rw [← hvalues c hc]
    exact composable_forest_subtree_nonzero S H sap letters hcomp root c hyield hramsey hcsub
  obtain ⟨i, P, hP, hReach, heq, hprod⟩ :=
    nonzero_idempotent_profile S H sap e henonzero he
  refine ⟨i, P, hP, hReach, hprod, ?_⟩
  intro d hd
  exact (hvalues d hd).trans heq

end
end CCO.OldIdempotentForest
