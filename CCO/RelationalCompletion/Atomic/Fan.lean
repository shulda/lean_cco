import CCO.RelationalCompletion.Atomic.Class

/-! Ordinary AP fan induction with all old root chords retained, over an
arbitrary typed palette. Unrecorded chords impose no requirement. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

def prefixEmbedding {a n : Nat} (vertices : Fin n ↪ Fin a) {k : Nat}
    (hk : k < n) : Fin (k+1) ↪ Fin a :=
  { toFun := fun p => vertices ⟨p.val, by omega⟩
    inj' := by intro p q h; exact Fin.ext (congrArg (fun z : Fin n => z.val) (vertices.injective h)) }

/-- The two displayed distinct vertices, with their original order. -/
def pairIndex {n : Nat} (x y : Fin n) (hne : x ≠ y) : Fin 2 ↪ Fin n where
  toFun p := if p.val = 0 then x else y
  inj' := by
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all

@[simp] theorem pairIndex_apply {n : Nat} (x y : Fin n) (hne : x ≠ y) (p : Fin 2) :
    pairIndex x y hne p = if p.val = 0 then x else y := rfl

def tripleIndex {n : Nat} (x y z : Fin n) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Fin 3 ↪ Fin n where
  toFun p := if p.val = 0 then x else if p.val = 1 then y else z
  inj' := by
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all

@[simp] theorem tripleIndex_apply {n : Nat} (x y z : Fin n)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (p : Fin 3) :
    tripleIndex x y z hxy hyz hxz p = if p.val = 0 then x else if p.val = 1 then y else z := rfl

/-- The complete two-point input base embeds into any target pair of exactly the same full colour. -/
def pairEmbeddingFromColour (A B : Model P) (x y : Fin A.size) (x' y' : Fin B.size)
    (hxy : x ≠ y) (hx'y' : x' ≠ y') (hcol : B.colour x' y' = A.colour x y) :
    Embedding (A.pullback (pairIndex x y hxy)) B := by
  have hs0 : B.tag x' = A.tag x := by
    exact (B.colour_fst x' y').symm.trans ((congrArg Sigma.fst hcol).trans (A.colour_fst x y))
  have hs1 : B.tag y' = A.tag y := by
    exact (B.colour_snd_fst x' y').symm.trans
      ((congrArg (fun c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom => c.2.1) hcol).trans (A.colour_snd_fst x y))
  refine { vertex := pairIndex x' y' hx'y', tag_eq := ?_, edge_eq := ?_ }
  · intro p
    fin_cases p
    · change B.tag x' = A.tag x
      exact hs0
    · change B.tag y' = A.tag y
      exact hs1
  · intro p q
    have hc : B.colour ((pairIndex x' y' hx'y') p) ((pairIndex x' y' hx'y') q) =
        (A.pullback (pairIndex x y hxy)).colour p q := by
      fin_cases p <;> fin_cases q
      · change B.colour x' x' = (A.pullback (pairIndex x y hxy)).colour 0 0
        rw [A.colour_pullback]
        change B.colour x' x' = A.colour x x
        rw [B.colour_self, A.colour_self, hs0]
      · change B.colour x' y' = (A.pullback (pairIndex x y hxy)).colour 0 1
        rw [A.colour_pullback]
        exact hcol
      · change B.colour y' x' = (A.pullback (pairIndex x y hxy)).colour 1 0
        rw [A.colour_pullback]
        change B.colour y' x' = A.colour y x
        rw [B.colour_reverse, A.colour_reverse, hcol]
      · change B.colour y' y' = (A.pullback (pairIndex x y hxy)).colour 1 1
        rw [A.colour_pullback]
        change B.colour y' y' = A.colour y y
        rw [B.colour_self, A.colour_self, hs1]
    exact congrArg (fun c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom => c.2.2) hc

def FanRealized (K : Model P → Prop) (A : Model P)
    {n : Nat} (vertices : Fin n ↪ Fin A.size) {k : Nat} (hk : k < n) : Prop :=
  let e := prefixEmbedding vertices hk
  ∃ B : Model P, K B ∧ ∃ point : Fin (k+1) → Fin B.size,
    (∀ p, B.tag (point p) = A.tag (e p)) ∧
    (∀ p : Fin k, B.colour (point p.castSucc) (point p.succ) = A.colour (e p.castSucc) (e p.succ)) ∧
    (∀ p, B.colour (point 0) (point p) = A.colour (e 0) (e p))

/-- The fan is realized in a MEMBER OF K at every step, using ordinary class AP. -/
theorem fanRealized (K : Model P → Prop) (A : Model P)
    (ap : AP K) (small : SmallSubmodels K A)
    {n : Nat} (vertices : Fin n ↪ Fin A.size) :
    ∀ {k : Nat} (hk : k < n) (_hkpos : 1 ≤ k), FanRealized K A vertices hk := by
  intro k
  induction k with
  | zero => intro hk hp; omega
  | succ k ih =>
    intro hk hp
    by_cases hzero : k = 0
    · subst k
      let e := prefixEmbedding vertices hk
      have hne : e 0 ≠ e (Fin.last 1) := e.injective.ne (by decide)
      let inds := pairIndex (e 0) (e (Fin.last 1)) hne
      let B := A.pullback inds
      have hKB : K B := small inds (by decide)
      let point : Fin 2 → Fin B.size := fun p => p
      refine ⟨B, hKB, point, ?_, ?_, ?_⟩
      · intro p
        fin_cases p <;> rfl
      · intro p
        fin_cases p
        exact A.colour_pullback inds 0 1
      · intro p
        fin_cases p <;> rfl
    · by_cases hone : k = 1
      · subst k
        let e := prefixEmbedding vertices hk
        let B := A.pullback e
        refine ⟨B, small e (by decide), (fun p => p), ?_, ?_, ?_⟩
        · intro p; rfl
        · intro p; rfl
        · intro p; rfl
      · have hkpos : 1 ≤ k := by omega
        have hkold : k < n := by omega
        obtain ⟨B, hKB, point, hsort, hpath, hstar⟩ := ih hkold hkpos
        let e := prefixEmbedding vertices hkold
        let e' := prefixEmbedding vertices hk
        have hrLast : e 0 ≠ e (Fin.last k) := e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this; omega)
        have hlastNext : e (Fin.last k) ≠ e' (Fin.last (k+1)) := by
          intro h
          have hh := congrArg Fin.val (vertices.injective h)
          simp at hh
        have hrNext : e 0 ≠ e' (Fin.last (k+1)) := by
          intro h
          have hh := congrArg Fin.val (vertices.injective h)
          simp at hh
        have hchord := hstar (Fin.last k)
        change B.colour (point 0) (point (Fin.last k)) = A.colour (e 0) (e (Fin.last k)) at hchord
        obtain ⟨a, ha⟩ := A.complete (e 0) (e (Fin.last k)) hrLast
        have hBpair : point 0 ≠ point (Fin.last k) := by
          apply B.ne_of_colour_some (i := A.tag (e 0)) (j := A.tag (e (Fin.last k))) (a := a)
          exact hchord.trans (by change (⟨A.tag (e 0), A.tag (e (Fin.last k)), A.diagram.edge (e 0) (e (Fin.last k))⟩ : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom) = _; rw [ha])
        let pair := pairIndex (e 0) (e (Fin.last k)) hrLast
        let triple := tripleIndex (e 0) (e (Fin.last k)) (e' (Fin.last (k+1))) hrLast hlastNext hrNext
        let E := A.pullback pair
        let Q := A.pullback triple
        have hKE : K E := small pair (by decide)
        have hKQ : K Q := small triple (by decide)
        let eEB : Embedding E B := pairEmbeddingFromColour A B _ _ _ _ hrLast hBpair hchord
        have hQpair : Q.colour 0 1 = A.colour (e 0) (e (Fin.last k)) := A.colour_pullback triple 0 1
        let eEQ : Embedding E Q := pairEmbeddingFromColour A Q _ _ 0 1 hrLast (by change (0 : Fin 3) ≠ 1; decide) hQpair
        obtain ⟨T, hKT, eBT, eQT, hbase⟩ := ap E B Q hKE hKB hKQ eEB eEQ
        have hroot : eBT.vertex (point 0) = eQT.vertex 0 := by
          have h := hbase 0
          exact h
        have hlast : eBT.vertex (point (Fin.last k)) = eQT.vertex 1 := by
          have h := hbase 1
          exact h
        let out : Fin (k+1) → Fin T.size := fun p => eBT.vertex (point p)
        let next : Fin T.size := eQT.vertex 2
        have hrootnext : T.colour (out 0) next = A.colour (e 0) (e' (Fin.last (k+1))) := by
          calc
            _ = T.colour (eQT.vertex 0) (eQT.vertex 2) := by change T.colour (eBT.vertex (point 0)) (eQT.vertex 2) = _; rw [hroot]
            _ = Q.colour 0 2 := eQT.preserves_colour 0 2
            _ = _ := A.colour_pullback triple 0 2
        have hlastnext : T.colour (out (Fin.last k)) next = A.colour (e (Fin.last k)) (e' (Fin.last (k+1))) := by
          calc
            _ = T.colour (eQT.vertex 1) (eQT.vertex 2) := by change T.colour (eBT.vertex (point (Fin.last k))) (eQT.vertex 2) = _; rw [hlast]
            _ = Q.colour 1 2 := eQT.preserves_colour 1 2
            _ = _ := A.colour_pullback triple 1 2
        let point' : Fin (k+2) → Fin T.size := fun p =>
          if h : p.val < k+1 then out ⟨p.val, h⟩ else next
        have hsort' : ∀ p, T.tag (point' p) = A.tag (e' p) := by
          intro p
          by_cases h : p.val < k+1
          · simp only [point', dite_eq_left h]
            exact (eBT.tag_eq _).trans (hsort _)
          · have hpLast : p = Fin.last (k+1) := by apply Fin.ext; simp; omega
            subst p
            simp only [point', Fin.val_last, dite_eq_right (Nat.lt_irrefl (k+1))]
            exact eQT.tag_eq (2 : Fin 3)
        have hpath' : ∀ p : Fin (k+1), T.colour (point' p.castSucc) (point' p.succ) =
            A.colour (e' p.castSucc) (e' p.succ) := by
          intro p
          by_cases h : p.val < k
          · have h1 : p.val < k+1 := by omega
            have h2 : p.val+1 < k+1 := by omega
            simp only [point', Fin.val_castSucc, Fin.val_succ, dite_eq_left h1, dite_eq_left h2]
            exact (eBT.preserves_colour _ _).trans (hpath ⟨p.val, h⟩)
          · have hpLast : p = Fin.last k := by apply Fin.ext; simp; omega
            subst p
            simp only [point', Fin.val_castSucc, Fin.val_succ, Fin.val_last,
              dite_eq_left (Nat.lt_succ_self k), dite_eq_right (Nat.lt_irrefl (k+1))]
            exact hlastnext
        have hstar' : ∀ p, T.colour (point' 0) (point' p) = A.colour (e' 0) (e' p) := by
          intro p
          have h0 : (0 : Nat) < k+1 := by omega
          by_cases h : p.val < k+1
          · simp only [point', Fin.val_zero, dite_eq_left h]
            exact (eBT.preserves_colour _ _).trans (hstar ⟨p.val, h⟩)
          · have hpLast : p = Fin.last (k+1) := by apply Fin.ext; simp; omega
            subst p
            simp only [point', Fin.val_zero, Fin.val_last,
              dite_eq_right (Nat.lt_irrefl (k+1))]
            exact hrootnext
        exact ⟨T, hKT, point', hsort', hpath', hstar'⟩
  
end CCO.RelationalCompletion.Atomic
