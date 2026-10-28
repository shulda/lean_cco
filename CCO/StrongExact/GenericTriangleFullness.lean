import CCO.StrongExact.FiniteAtomicClass

/-!
# Triangle fullness for an arbitrary hereditary finite complete atomic class

The fan targets are members of the arbitrary class K. Ordinary AP glues these
K-models over complete edges; semantic class CCO supplies a K-target for the
whole complete input; its homomorphism is an induced embedding and heredity
returns the input itself to K. No original-source realization, homogeneous
limit, SAP or representation provider is assumed.
-/

universe u v w
namespace CCO.FiniteAtomicClass
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

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
def pairEmbeddingFromColour (A B : Model S) (x y : Fin A.size) (x' y' : Fin B.size)
    (hxy : x ≠ y) (hx'y' : x' ≠ y') (hcol : B.colour x' y' = A.colour x y) :
    Embedding (A.pullback (pairIndex x y hxy)) B := by
  have hs0 : B.sort x' = A.sort x := by
    exact (B.colour_fst x' y').symm.trans ((congrArg Sigma.fst hcol).trans (A.colour_fst x y))
  have hs1 : B.sort y' = A.sort y := by
    exact (B.colour_snd_fst x' y').symm.trans
      ((congrArg (fun c : Σ i : ι, Σ j : ι, Option (S.Atom i j) => c.2.1) hcol).trans (A.colour_snd_fst x y))
  refine { vertex := pairIndex x' y' hx'y', preserves_sort := ?_, preserves_colour := ?_ }
  · intro p
    fin_cases p
    · change B.sort x' = A.sort x
      exact hs0
    · change B.sort y' = A.sort y
      exact hs1
  · intro p q
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

def FanRealized (K : Model S → Prop) (A : Model S)
    {n : Nat} (vertices : Fin n ↪ Fin A.size) {k : Nat} (hk : k < n) : Prop :=
  let e := CompleteDiagram.prefixEmbedding vertices hk
  ∃ B : Model S, K B ∧ ∃ point : Fin (k+1) → Fin B.size,
    (∀ p, B.sort (point p) = A.sort (e p)) ∧
    (∀ p : Fin k, B.colour (point p.castSucc) (point p.succ) = A.colour (e p.castSucc) (e p.succ)) ∧
    B.colour (point 0) (point (Fin.last k)) = A.colour (e 0) (e (Fin.last k))

/-- The fan is realized in a MEMBER OF K at every step, using ordinary class AP. -/
theorem fanRealized (K : Model S → Prop) (A : Model S)
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
      let e := CompleteDiagram.prefixEmbedding vertices hk
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
      · exact A.colour_pullback inds 0 1
    · have hkpos : 1 ≤ k := by omega
      have hkold : k < n := by omega
      obtain ⟨B, hKB, point, hsort, hpath, hchord⟩ := ih hkold hkpos
      let e := CompleteDiagram.prefixEmbedding vertices hkold
      let e' := CompleteDiagram.prefixEmbedding vertices hk
      have hrLast : e 0 ≠ e (Fin.last k) := e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this; omega)
      have hlastNext : e (Fin.last k) ≠ e' (Fin.last (k+1)) := by
        intro h
        have hh := congrArg Fin.val (vertices.injective h)
        simp at hh
      have hrNext : e 0 ≠ e' (Fin.last (k+1)) := by
        intro h
        have hh := congrArg Fin.val (vertices.injective h)
        simp at hh
      change B.colour (point 0) (point (Fin.last k)) = A.colour (e 0) (e (Fin.last k)) at hchord
      obtain ⟨a, ha⟩ := A.diagram.complete (e 0) (e (Fin.last k)) hrLast
      have hBpair : point 0 ≠ point (Fin.last k) := by
        apply B.ne_of_colour_some (a := a)
        exact hchord.trans (by simp [Model.colour, hrLast, ha])
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
      have hsort' : ∀ p, T.sort (point' p) = A.sort (e' p) := by
        intro p
        by_cases h : p.val < k+1
        · simp only [point', dite_eq_left h]
          exact (eBT.preserves_sort _).trans (hsort _)
        · have hpLast : p = Fin.last (k+1) := by apply Fin.ext; simp; omega
          subst p
          simp only [point', Fin.val_last, dite_eq_right (Nat.lt_irrefl (k+1))]
          exact eQT.preserves_sort (2 : Fin 3)
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
      have hchord' : T.colour (point' 0) (point' (Fin.last (k+1))) =
          A.colour (e' 0) (e' (Fin.last (k+1))) := by
        simp only [point', Fin.val_zero, Fin.val_last, dite_eq_right (Nat.lt_irrefl (k+1))]
        exact hrootnext
      exact ⟨T, hKT, point', hsort', hpath', hchord'⟩

/-- Every specified simple cycle of the complete input maps to some actual K-model.
No condition on its unused chords is imposed on the cycle homomorphism. -/
theorem cycleHomInto_of_AP (K : Model S → Prop) (A : Model S)
    (ap : AP K) (small : SmallSubmodels K A) (C : SimpleCycle A.diagram.diagram) :
    ∃ B : Model S, K B ∧ CycleHomInto C B := by
  classical
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  have hk : C.length - 1 < C.length := by have := C.length_pos; omega
  have hpos : 1 ≤ C.length - 1 := by have := C.length_ge_three; omega
  have hlen : C.length - 1 + 1 = C.length := by have := C.length_pos; omega
  obtain ⟨B, hKB, point, hsort, hpath, hchord⟩ := fanRealized K A ap small C.vertices hk hpos
  let pointN : Fin C.length → Fin B.size := fun p => point (Fin.cast hlen.symm p)
  have hsortN : ∀ p, B.sort (pointN p) = A.sort (C.vertices p) := by
    intro p
    exact hsort (Fin.cast hlen.symm p)
  have hcolour : ∀ p, B.colour (pointN p) (pointN (cyclicNext C.length_pos p)) =
      A.colour (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) := by
    intro p
    by_cases hlast : p.val = C.length - 1
    · have hp : p = ⟨C.length - 1, hk⟩ := Fin.ext hlast
      have hn : cyclicNext C.length_pos p = 0 := by
        apply Fin.ext
        simp only [cyclicNext, Fin.val_zero]
        rw [hlast, hlen, Nat.mod_self]
      have hback : B.colour (pointN ⟨C.length - 1, hk⟩) (pointN 0) =
          A.colour (C.vertices ⟨C.length - 1, hk⟩) (C.vertices 0) := by
        calc
          _ = reverseTagged S (B.colour (point 0) (point (Fin.last (C.length-1)))) := B.colour_reverse _ _
          _ = _ := congrArg (reverseTagged S) hchord
          _ = _ := (A.colour_reverse _ _).symm
      simpa only [← hp, hn] using hback
    · have hlt : p.val < C.length - 1 := by omega
      have hn : cyclicNext C.length_pos p = ⟨p.val+1, by omega⟩ := by
        apply Fin.ext
        simp only [cyclicNext]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [hn]
      change B.colour (point ⟨p.val, by omega⟩) (point ⟨p.val+1, by omega⟩) =
        A.colour (C.vertices p) (C.vertices ⟨p.val+1, by omega⟩)
      exact hpath ⟨p.val, hlt⟩
  refine ⟨B, hKB, pointN, hsortN, ?_⟩
  intro p a ha
  exact (hcolour p).trans (by simp [Model.colour, C.next_ne p, ha])

/-- AP and semantic homomorphic CCO imply triangle fullness for an arbitrary
hereditary class of finite complete atomic structures over the given palette.
There is NO actual-age, ambient source, homogeneity, SAP or representation premise. -/
theorem triangleFullness (K : Model S → Prop) (hereditary : Hereditary K)
    (ap : AP K) (cco : SemanticCCO.{u,v,w,0} K) (A : Model S) (small : SmallSubmodels K A) : K A := by
  obtain ⟨B, hKB, ⟨f⟩⟩ := cco (Fin A.size) A.diagram.diagram (cycleHomInto_of_AP K A ap small)
  exact hereditary ⟨f.toEmbedding⟩ hKB

end CCO.FiniteAtomicClass
