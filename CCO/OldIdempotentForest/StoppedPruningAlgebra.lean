import CCO.OldIdempotentForest.StoppedPruning

/-! Every positive middle block consists of a positive number of original
children of one common idempotent value. Its WHOLE original yield has that
same value. Empty-word evaluation and a semigroup unit are never used. -/

universe u v
namespace CCO.OldIdempotentForest

theorem eval_listValue_constant {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M)
    (hmul : ∀ x y, x ≠ [] → y ≠ [] → eval (x ++ y) = eval x * eval y)
    (e : M) (he : e * e = e) (children : List (FactorizationTree A))
    (hchildren : children ≠ [])
    (hne : ∀ t ∈ children, t.value ≠ [])
    (hvalue : ∀ t ∈ children, eval t.value = e) :
    eval (FactorizationTree.listValue children) = e := by
  induction children with
  | nil => exact False.elim (hchildren rfl)
  | cons first rest ih =>
    cases rest with
    | nil => simpa only [FactorizationTree.listValue_cons,FactorizationTree.listValue_nil,
        List.append_nil] using hvalue first (by simp)
    | cons second tail =>
      have hrest : FactorizationTree.listValue (second :: tail) ≠ [] := by
        intro hz
        have hs := hne second (by simp)
        rw [FactorizationTree.listValue_cons] at hz
        exact hs (List.append_eq_nil_iff.mp hz).1
      rw [FactorizationTree.listValue_cons,
        hmul _ _ (hne first (by simp)) hrest,hvalue first (by simp)]
      have hr := ih (by simp) (fun t ht => hne t (by simp [ht]))
        (fun t ht => hvalue t (by simp [ht]))
      rw [hr,he]

theorem PruningTree.gap_piece_iff {A : Type u} (p : PruningTree A)
    (g : List A) (hg : g ≠ []) :
    Piece.gap g hg ∈ p.pieces ↔ g ∈ p.gapWords := by
  classical
  induction p with
  | leaf a => simp [PruningTree.pieces,PruningTree.gapWords]
  | branch l middle r ihl ihr =>
    by_cases hm : middle = [] <;>
      simp [PruningTree.pieces,PruningTree.gapWords,hm,ihl,ihr]

/-- C24: the actual original word of EVERY recorded maximal gap has an
idempotent value. This theorem is independent of forest existence and of
the source-specific nonzero argument. -/
theorem Prunes.gap_idempotent {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M)
    (hmul : ∀ x y, x ≠ [] → y ≠ [] → eval (x ++ y) = eval x * eval y)
    {t : FactorizationTree A} {p : PruningTree A} (hp : Prunes t p)
    (ht : t.IsRamsey eval) {g : List A} (hg : g ∈ p.gapWords) :
    IsIdempotentElem (eval g) := by
  induction hp with
  | leaf a => simp [PruningTree.gapWords] at hg
  | binary hl hr ihl ihr =>
    rw [FactorizationTree.isRamsey_binary] at ht
    simp [PruningTree.gapWords] at hg
    rcases hg with hg | hg
    · exact ihl ht.1 hg
    · exact ihr ht.2 hg
  | @idempotent l r middle pl pr hl hr ihl ihr =>
    rw [FactorizationTree.isRamsey_idempotent,FactorizationTree.listIsRamsey_iff] at ht
    simp only [PruningTree.gapWords,List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact ihl (ht.2.1 l (by simp)) hg
    · split at hg
      · simp at hg
      · have hgEq : g = FactorizationTree.listValue middle := List.mem_singleton.mp hg
        subst g
        obtain ⟨e,he,hvalues⟩ := ht.2.2
        have hmiddle : middle ≠ [] := by
          intro hz
          exact ‹FactorizationTree.listValue middle ≠ []› (by simp [hz])
        have hval := eval_listValue_constant eval hmul e he middle hmiddle
          (fun child hc => FactorizationTree.tree_value_ne_nil child (ht.2.1 child (by simp [hc])))
          (fun child hc => hvalues child (by simp [hc]))
        rw [hval]
        exact he
    · exact ihr (ht.2.1 r (by simp)) hg

theorem Prunes.located_gap_idempotent {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M)
    (hmul : ∀ x y, x ≠ [] → y ≠ [] → eval (x ++ y) = eval x * eval y)
    {t : FactorizationTree A} {p : PruningTree A} (hp : Prunes t p)
    (ht : t.IsRamsey eval) {q : LocatedPiece A} (hq : q ∈ locate 0 p.pieces)
    {g : List A} (hg : g ≠ []) (hgap : q.piece = .gap g hg) :
    IsIdempotentElem (eval g) := by
  have hmem := locate_piece_mem hq
  rw [hgap] at hmem
  exact hp.gap_idempotent eval hmul ht ((p.gap_piece_iff g hg).mp hmem)

end CCO.OldIdempotentForest
