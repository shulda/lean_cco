import CCO.Selectors.LoopPowers
import CCO.PairHomogeneity

/-! The FULL invariant-equivalence NR2 condition on actual named sorts.
Relative index two is given by its literal two-class decomposition in each
upper class, so no finiteness/exactness restriction on either equivalence
is hidden in the condition. -/
universe u v w t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {i : ι}

def InvariantSetoid (R : Setoid (X i)) : Prop :=
  ∀ (g : G) x y, R.r (g • x) (g • y) ↔ R.r x y

/-- Every upper class is exactly the union of two DISTINCT lower classes. -/
def RelativeIndexTwo (R T : Setoid (X i)) : Prop :=
  (∀ x y, R.r x y → T.r x y) ∧
  ∀ x, ∃ y, T.r x y ∧ ¬ R.r x y ∧
    ∀ z, T.r x z ↔ R.r x z ∨ R.r y z

/-- NR2 quantifies over ALL invariant equivalences on every original sort. -/
def FullNR2 (_source : AtomicSource.{u,v,w} ι X) : Prop :=
  ∀ (i : ι) (R T : Setoid (X i)),
    InvariantSetoid (G := G) R → InvariantSetoid (G := G) T →
    RelativeIndexTwo R T → False

def eqOrMenu (P : S.Menu i i) (x y : X i) : Prop := x = y ∨ S.menuRel P x y

private theorem menu_symm (P : S.Menu i i) {x y : X i}
    (h : S.menuRel P x y) : S.menuRel P y x := by
  obtain ⟨a, ha, hc⟩ := h
  exact ⟨a, ha, by simpa only [S.symmetricLoop] using (S.colour_swap x y a).mp hc⟩

private theorem menu_comp (P Q : S.Menu i i) {x y z : X i}
    (hxy : S.menuRel P x y) (hyz : S.menuRel Q y z) (hxz : x ≠ z) :
    S.menuRel (S.product P Q) x z := by
  obtain ⟨a, ha, hc⟩ := hxy
  obtain ⟨b, hb, hd⟩ := hyz
  have htag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,z⟩ := by
    intro he
    exact hxz (by simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using he)
  obtain ⟨c, hc'⟩ := S.some_colour_of_ne x z htag
  exact ⟨c, ⟨a, ha, b, hb, x, y, z, hc, hd, hc'⟩, hc'⟩

def menuSetoid (P : S.Menu i i) (closed : S.product P P ⊆ P) : Setoid (X i) where
  r := eqOrMenu S P
  iseqv := ⟨fun _ => Or.inl rfl, by
    intro x y h
    exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (menu_symm S P h)), by
    intro x y z hxy hyz
    rcases hxy with he | hxy
    · subst y; exact hyz
    rcases hyz with he | hyz
    · subst z; exact Or.inr hxy
    by_cases he : x = z
    · exact Or.inl he
    · obtain ⟨c,hc,hcol⟩ := menu_comp S P P hxy hyz he
      exact Or.inr ⟨c,closed hc,hcol⟩⟩

private theorem eqOrMenu_invariant (H : HomogeneousSource S G) (P : S.Menu i i) :
    ∀ (g : G) x y, eqOrMenu S P (g • x) (g • y) ↔ eqOrMenu S P x y := by
  intro g x y
  have hc := S.colourInvariant_of_homogeneous H (i := i) (j := i) g x y
  constructor
  · rintro (he | ⟨a,ha,hcol⟩)
    · exact Or.inl (MulAction.injective g he)
    · exact Or.inr ⟨a,ha,hc.symm.trans hcol⟩
  · rintro (he | ⟨a,ha,hcol⟩)
    · exact Or.inl (congrArg (fun z => g • z) he)
    · exact Or.inr ⟨a,ha,hc.trans hcol⟩

theorem menuSetoid_invariant (H : HomogeneousSource S G) (P : S.Menu i i)
    (closed : S.product P P ⊆ P) : InvariantSetoid (G := G) (menuSetoid S P closed) :=
  eqOrMenu_invariant S H P

private theorem menu_neighbour (H : HomogeneousSource S G) (P : S.Menu i i)
    (hP : P.Nonempty) (x : X i) : ∃ y, S.menuRel P x y := by
  obtain ⟨a,ha⟩ := hP
  obtain ⟨z,y,hzy⟩ := S.realized a
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i z x
  refine ⟨g • y,a,ha,?_⟩
  have hc := S.colourInvariant_of_homogeneous H (i := i) (j := i) g z y
  simpa only [hg] using hc.trans hzy

/-- The stable parity identities create a full index-two interval if the
positive even and odd diversity menus are disjoint. -/
theorem parity_index_two (H : HomogeneousSource S G)
    (J O : S.Menu i i) (hO : O.Nonempty)
    (hJJ : S.product J J = J) (hJO : S.product J O = O)
    (hOO : S.product O O = J) (hdis : Disjoint J O) :
    ∃ R T : Setoid (X i), InvariantSetoid (G := G) R ∧
      InvariantSetoid (G := G) T ∧ RelativeIndexTwo R T := by
  have hOJ : S.product O J = O := (S.loop_product_commute O J).trans hJO
  have hclosedJ : S.product J J ⊆ J := by rw [hJJ]
  have hclosedU : S.product (J ∪ O) (J ∪ O) ⊆ J ∪ O := by
    rintro c ⟨a,ha,b,hb,ht⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by rw [←hJJ]; exact ⟨a,ha,b,hb,ht⟩)
    · exact Or.inr (by rw [←hJO]; exact ⟨a,ha,b,hb,ht⟩)
    · exact Or.inr (by rw [←hOJ]; exact ⟨a,ha,b,hb,ht⟩)
    · exact Or.inl (by rw [←hOO]; exact ⟨a,ha,b,hb,ht⟩)
  let R := menuSetoid S J hclosedJ
  let T := menuSetoid S (J ∪ O) hclosedU
  refine ⟨R,T,menuSetoid_invariant S H _ _,menuSetoid_invariant S H _ _,?_,?_⟩
  · intro x y h
    rcases h with he | ⟨a,ha,hcol⟩
    · exact Or.inl he
    · exact Or.inr ⟨a,Or.inl ha,hcol⟩
  · intro x
    obtain ⟨y,hxy⟩ := menu_neighbour S H O hO x
    refine ⟨y,Or.inr ?_,?_,?_⟩
    · obtain ⟨a,ha,hcol⟩ := hxy
      exact ⟨a,Or.inr ha,hcol⟩
    · rintro (he | ⟨a,ha,hcol⟩)
      · subst y
        exact S.menuRel_ne hxy rfl
      · obtain ⟨b,hb,hcol'⟩ := hxy
        have he : a = b := Option.some.inj (hcol.symm.trans hcol')
        exact Set.disjoint_left.mp hdis ha (he.symm ▸ hb)
    · intro z
      constructor
      · rintro (he | ⟨a,ha,hcol⟩)
        · exact Or.inl (Or.inl he)
        rcases ha with ha | ha
        · exact Or.inl (Or.inr ⟨a,ha,hcol⟩)
        · by_cases he : y = z
          · exact Or.inr (Or.inl he)
          · have hc := menu_comp S O O (menu_symm S O hxy) ⟨a,ha,hcol⟩ he
            rw [hOO] at hc
            exact Or.inr (Or.inr hc)
      · rintro (h | h)
        · exact h.elim (fun he => Or.inl he) (fun ⟨a,ha,hcol⟩ =>
            Or.inr ⟨a,Or.inl ha,hcol⟩)
        · rcases h with he | hyz
          · subst z
            obtain ⟨a,ha,hcol⟩ := hxy
            exact Or.inr ⟨a,Or.inr ha,hcol⟩
          · by_cases he : x = z
            · exact Or.inl he
            · have hc := menu_comp S O J hxy hyz he
              rw [hOJ] at hc
              obtain ⟨a,ha,hcol⟩ := hc
              exact Or.inr ⟨a,Or.inr ha,hcol⟩

theorem parity_equal_of_nr2 (H : HomogeneousSource S G)
    (nr2 : FullNR2 S (G := G)) (point : S.RealPointGluing)
    (J O : S.Menu i i) (hJJ : S.product J J = J)
    (hJO : S.product J O = O) (hOO : S.product O O = J)
    (hO : O.Nonempty) : J = O := by
  by_cases hd : Disjoint J O
  · obtain ⟨R,T,hR,hT,h2⟩ := parity_index_two S H J O hO hJJ hJO hOO hd
    exact False.elim (nr2 i R T hR hT h2)
  · have hi : (J ∩ O).Nonempty := Set.not_disjoint_iff.mp hd
    obtain ⟨t,htJ,htO⟩ := hi
    have hJt : S.product J ({t} : S.Menu i i) = J := by
      apply Set.Subset.antisymm
      · intro c hc
        rw [←hJJ]
        exact S.product_mono (fun _ h => h) (by intro a ha; simpa only [Set.mem_singleton_iff] using ha ▸ htJ) hc
      · intro r hr
        obtain ⟨s,hs⟩ := point r t
        have hsJ : s ∈ J := by rw [←hJJ]; exact ⟨r,hr,t,htJ,hs⟩
        refine ⟨s,hsJ,t,by simp,?_⟩
        simpa only [S.symmetricLoop] using S.triangle_rotate hs
    have hJOsub : J ⊆ O := by
      intro c hc
      rw [←hJO]
      rw [←hJt] at hc
      exact S.product_mono (fun _ h => h) (by intro a ha; simpa only [Set.mem_singleton_iff] using ha ▸ htO) hc
    apply Set.Subset.antisymm hJOsub
    intro c hc
    rw [←hOO]
    rw [←hJO] at hc
    exact S.product_mono hJOsub (fun _ h => h) hc

/-- Actual full-sort NR2 collapses the two stable parity values. No CCO
hypothesis occurs. Positive exponent n+1 is represented by index n. -/
theorem loopPower_eventually_constant (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : FullNR2 S (G := G))
    (P : S.Menu i i) (hP : P.Nonempty) :
    ∃ N : Nat, ∀ n, N ≤ n → loopPower S P n = loopPower S P (n+1) := by
  let point : S.RealPointGluing := S.realPointGluing_of_SAP H sap
  let edge : S.RealEdgeGluing := S.realEdgeGluing_of_SAP H sap
  obtain ⟨N,hJ,hO,hJJ,hJO,hOO,hPO,hE,hO'⟩ := loopPower_even_odd S point edge P hP
  have heq := parity_equal_of_nr2 S H nr2 point _ _ hJJ hJO hOO hO
  refine ⟨2*N+1,?_⟩
  intro n hn
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm
  · let k := n / 2
    have hk : n = 2*k := by omega
    have hNk : N ≤ k := by omega
    have hnext : n+1 = 2*k+1 := by omega
    rw [hnext,hk,hO' k hNk,hE k hNk]
    exact heq.symm
  · let k := n / 2
    have hk : n = 2*k+1 := by omega
    have hNk : N ≤ k := by omega
    have hnext : n+1 = 2*(k+1) := by omega
    rw [hnext,hk,hE k hNk,hO' (k+1) (by omega)]
    exact heq

/-- Full invariant equivalences described by original pair colours, without
naming a witness group. Under homogeneity these are exactly the group-invariant
relations, including the true diagonal. -/
def ColourInvariantSetoid (R : Setoid (X i)) : Prop :=
  ∀ x y x' y', S.colour x y = S.colour x' y' → (R.r x y ↔ R.r x' y')

def OriginalNR2 : Prop :=
  ∀ (i : ι) (R T : Setoid (X i)),
    ColourInvariantSetoid S R → ColourInvariantSetoid S T → RelativeIndexTwo R T → False

theorem colourInvariantSetoid_of_invariant (H : HomogeneousSource S G)
    (R : Setoid (X i)) (hR : InvariantSetoid (G := G) R) :
    ColourInvariantSetoid S R := by
  intro x y x' y' hc
  obtain ⟨g,hx,hy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
  simpa only [hx,hy] using (hR g x y).symm

theorem invariantSetoid_of_colourInvariant (H : HomogeneousSource S G)
    (R : Setoid (X i)) (hR : ColourInvariantSetoid S R) :
    InvariantSetoid (G := G) R := by
  intro g x y
  exact hR _ _ _ _ (S.colourInvariant_of_homogeneous H g x y)


theorem fullNR2_of_original (H : HomogeneousSource S G) (nr2 : OriginalNR2 S) :
    FullNR2 S (G := G) := by
  intro i R T hR hT htwo
  exact nr2 i R T (colourInvariantSetoid_of_invariant S H R hR)
    (colourInvariantSetoid_of_invariant S H T hT) htwo

/-- Pair homogeneity identifies the two full invariant-equivalence descriptions. -/
theorem fullNR2_iff_original (H : HomogeneousSource S G) :
    FullNR2 S (G := G) ↔ OriginalNR2 S := by
  constructor
  · intro nr2 i R T hR hT htwo
    exact nr2 i R T (invariantSetoid_of_colourInvariant S H R hR)
      (invariantSetoid_of_colourInvariant S H T hT) htwo
  · exact fullNR2_of_original S H


theorem loopPower_constant_tail (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : FullNR2 S (G := G))
    (P : S.Menu i i) (hP : P.Nonempty) :
    ∃ N : Nat, ∀ n, N ≤ n → loopPower S P n = loopPower S P N := by
  obtain ⟨N,hN⟩ := loopPower_eventually_constant S H sap nr2 P hP
  refine ⟨N,?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hN n hn).symm.trans ih

end CCO.Selectors
