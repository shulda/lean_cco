import CCO.SafeReadings.NoReturn
import CCO.SafeReadings.CentralActions
import CCO.SafeReadings.LoopReturn
import Mathlib.GroupTheory.OrderOfElement

/-! Parametric positive return contexts. The SAME return operation acts on
all parallel raw menus; the explicit bound counts its iterations. -/
universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

/-- A central tagged equality is required for EVERY input. Outside factors
are genuine nonempty menus or absent identity operations. -/
inductive UniformNormalForm {i j k l : ι} (T : S.Menu i j → S.Menu k l) :
    Λ → Bool → Bool → Prop
  | forward (g : Λ) {a b} (C : S.Menu i j → S.Menu a b)
      (central : ∀ D, A.act g (⟨i,j,D⟩ : TaggedMenu S) = ⟨a,b,C D⟩)
      (L : PositiveOutside S k a) (R : PositiveOutside S b l)
      (value : ∀ D, T D = L.left (PositiveOutside.right (C D) R)) :
      UniformNormalForm T g false (L.positive || R.positive)
  | reverse (g : Λ) {a b} (C : S.Menu i j → S.Menu a b)
      (central : ∀ D, A.act g (⟨i,j,D⟩ : TaggedMenu S) = ⟨a,b,C D⟩)
      (L : PositiveOutside S k b) (R : PositiveOutside S a l)
      (value : ∀ D, T D = L.left (PositiveOutside.right (S.opposite (C D)) R)) :
      UniformNormalForm T g true (L.positive || R.positive)

private theorem central_source {i j a b : ι} (g : Λ)
    (C : S.Menu i j → S.Menu a b)
    (hc : ∀ D, A.act g (⟨i,j,D⟩ : TaggedMenu S) = ⟨a,b,C D⟩) : a = A.tag g i :=
  (congrArg Sigma.fst (hc ∅)).symm.trans (A.source g ⟨i,j,∅⟩)

private theorem central_target {i j a b : ι} (g : Λ)
    (C : S.Menu i j → S.Menu a b)
    (hc : ∀ D, A.act g (⟨i,j,D⟩ : TaggedMenu S) = ⟨a,b,C D⟩) : b = A.tag g j :=
  (congrArg (fun D : TaggedMenu S => D.2.1) (hc ∅)).symm.trans (A.target g ⟨i,j,∅⟩)

private theorem central_value {i j : ι} (g : Λ)
    (C : S.Menu i j → S.Menu (A.tag g i) (A.tag g j))
    (hc : ∀ D, A.act g (⟨i,j,D⟩ : TaggedMenu S) =
      ⟨A.tag g i,A.tag g j,C D⟩) (D : S.Menu i j) : C D = A.menuAct g D := by
  have he := (hc D).symm.trans (A.tagged_menuAct g D).symm
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he

variable (point : S.RealPointGluing) (edge : S.RealEdgeGluing)

include point edge in
/-- Composition concatenates positive factors. It never removes the last
present factor; central controls multiply and converse orientations add mod 2. -/
theorem UniformNormalForm.comp {i j k l m n : ι}
    {T : S.Menu k l → S.Menu m n} {U : S.Menu i j → S.Menu k l}
    {g h : Λ} {eps eta p q : Bool}
    (hT : UniformNormalForm S A T g eps p) (hU : UniformNormalForm S A U h eta q) :
    UniformNormalForm S A (T ∘ U) (g*h) (Bool.xor eps eta) (p || q) := by
  cases hT with
  | forward C hc L R hvalue =>
    have ha := central_source S A g C hc
    have hb := central_target S A g C hc
    cases ha; cases hb
    have hC := central_value S A g C hc
    cases hU with
    | forward D hd P Q hUvalue =>
      have hn := UniformNormalForm.forward (S := S) (A := A) (T := T ∘ U) (g*h)
        (fun E => A.menuAct g (D E))
        (fun E => by rw [A.mul,hd,← A.tagged_menuAct])
        (L.comp point (P.move A g)) ((Q.move A g).comp point R)
        (by intro E; simp only [Function.comp_apply,hvalue,hC,hUvalue,PositiveOutside.move_left,
          PositiveOutside.move_right,PositiveOutside.left_comp point edge,
          ← PositiveOutside.right_comp point edge,PositiveOutside.left_right edge])
      simpa only [PositiveOutside.positive_comp,PositiveOutside.positive_move,
        Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm] using hn
    | reverse D hd P Q hUvalue =>
      have hn := UniformNormalForm.reverse (S := S) (A := A) (T := T ∘ U) (g*h)
        (fun E => A.menuAct g (D E))
        (fun E => by rw [A.mul,hd,← A.tagged_menuAct])
        (L.comp point (P.move A g)) ((Q.move A g).comp point R)
        (by intro E; simp only [Function.comp_apply,hvalue,hC,hUvalue,PositiveOutside.move_left,
          PositiveOutside.move_right,A.menuAct_opposite,PositiveOutside.left_comp point edge,
          ← PositiveOutside.right_comp point edge,PositiveOutside.left_right edge])
      simpa only [PositiveOutside.positive_comp,PositiveOutside.positive_move,
        Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm] using hn
  | reverse C hc L R hvalue =>
    have ha := central_source S A g C hc
    have hb := central_target S A g C hc
    cases ha; cases hb
    have hC := central_value S A g C hc
    cases hU with
    | forward D hd P Q hUvalue =>
      have hn := UniformNormalForm.reverse (S := S) (A := A) (T := T ∘ U) (g*h)
        (fun E => A.menuAct g (D E))
        (fun E => by rw [A.mul,hd,← A.tagged_menuAct])
        (L.comp point (Q.move A g).opposite) ((P.move A g).opposite.comp point R)
        (by
          intro E
          simp only [Function.comp_apply]
          rw [hvalue,hC,hUvalue,PositiveOutside.move_left,PositiveOutside.move_right,
            PositiveOutside.opposite_left_right edge]
          simp only [PositiveOutside.left_comp point edge,← PositiveOutside.right_comp point edge,
            PositiveOutside.left_right edge])
      simpa only [PositiveOutside.positive_comp,PositiveOutside.positive_move,
        PositiveOutside.positive_opposite,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm] using hn
    | reverse D hd P Q hUvalue =>
      have hn := UniformNormalForm.forward (S := S) (A := A) (T := T ∘ U) (g*h)
        (fun E => A.menuAct g (D E))
        (fun E => by rw [A.mul,hd,← A.tagged_menuAct])
        (L.comp point (Q.move A g).opposite) ((P.move A g).opposite.comp point R)
        (by
          intro E
          simp only [Function.comp_apply]
          rw [hvalue,hC,hUvalue,PositiveOutside.move_left,PositiveOutside.move_right,
            A.menuAct_opposite,PositiveOutside.opposite_left_right edge,S.opposite_opposite]
          simp only [PositiveOutside.left_comp point edge,← PositiveOutside.right_comp point edge,
            PositiveOutside.left_right edge])
      simpa only [PositiveOutside.positive_comp,PositiveOutside.positive_move,
        PositiveOutside.positive_opposite,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm] using hn


include point edge in
/-- Iteration of a forward context retains its genuine positive factor. -/
theorem UniformNormalForm.iterate_forward {i j : ι} {T : S.Menu i j → S.Menu i j}
    {g : Λ} (hT : UniformNormalForm S A T g false true) (n : Nat) :
    UniformNormalForm S A (T^[n+1]) (g^(n+1)) false true := by
  induction n with
  | zero => simpa only [Nat.zero_add,pow_one,Function.iterate_one] using hT
  | succ n ih =>
    have hn := UniformNormalForm.comp S A point edge hT ih
    simpa only [Bool.false_xor,Bool.or_self,← pow_succ',Function.iterate_succ'] using hn

/-- With the central control literally one and no converse, the operation
is a pair of actual endpoint-loop multipliers. -/
theorem UniformNormalForm.identity_sandwich {i j : ι} {T : S.Menu i j → S.Menu i j}
    {p : Bool} (hT : UniformNormalForm S A T 1 false p) :
    ∃ (L : PositiveOutside S i i) (R : PositiveOutside S j j),
      (L.positive || R.positive) = p ∧ T = PositiveOutside.sandwich L R := by
  cases hT with
  | forward C hc L R hvalue =>
    have ha : _ = i := (congrArg Sigma.fst (hc ∅)).symm.trans
      (congrArg Sigma.fst (A.one (⟨i,j,∅⟩ : TaggedMenu S)))
    have hb : _ = j := (congrArg (fun D : TaggedMenu S => D.2.1) (hc ∅)).symm.trans
      (congrArg (fun D : TaggedMenu S => D.2.1) (A.one (⟨i,j,∅⟩ : TaggedMenu S)))
    dsimp only at ha hb
    cases ha; cases hb
    have hC (D : S.Menu i j) : C D = D := by
      have he := (hc D).symm.trans (A.one ⟨i,j,D⟩)
      simpa using he
    refine ⟨L,R,rfl,?_⟩
    funext D
    rw [hvalue,hC]
    rfl

include point edge in
/-- q=2|Gamma| clears BOTH the central group action and converse, preserving
at least one actual positive outside loop. No faithful action is required. -/
theorem UniformNormalForm.cleared_sandwich [Finite Λ] {i j : ι}
    {T : S.Menu i j → S.Menu i j} {g : Λ} {eps : Bool}
    (hT : UniformNormalForm S A T g eps true) :
    ∃ (L : PositiveOutside S i i) (R : PositiveOutside S j j),
      (L.positive || R.positive) = true ∧
      T^[2 * Nat.card Λ] = PositiveOutside.sandwich L R := by
  have hs := UniformNormalForm.comp S A point edge hT hT
  have hs' : UniformNormalForm S A (T^[2]) (g*g) false true := by
    simpa only [Bool.xor_self,Bool.or_self,Function.iterate_succ,Function.iterate_zero,
      Function.id_comp] using hs
  have hn := UniformNormalForm.iterate_forward S A point edge hs' (Nat.card Λ-1)
  have hc : 0 < Nat.card Λ := Nat.card_pos
  rw [Nat.sub_one_add_one_eq_of_pos hc,pow_card_eq_one',← Function.iterate_mul] at hn
  exact UniformNormalForm.identity_sandwich S A hn

variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

include point edge in
/-- C16 quantitative source theorem: the SAME return fills EVERY nonempty
parallel raw menu in 4|Gamma|m0 iterations, without exactness, S or CCO. -/
theorem uniform_return_iterate_full [Finite Λ]
    (H : HomogeneousSource S G) (primitive : SortwisePrimitive S)
    {i j : ι} {T : S.Menu i j → S.Menu i j} {g : Λ} {eps : Bool}
    (hT : UniformNormalForm S A T g eps true)
    (m0 : Nat) (hm0 : 0 < m0)
    (hi : Nat.card (S.Atom i i) ≤ m0) (hj : Nat.card (S.Atom j j) ≤ m0)
    (D : S.Menu i j) (hD : D.Nonempty) :
    T^[4 * Nat.card Λ * m0] D = Set.univ := by
  obtain ⟨L,R,hpos,hclear⟩ := UniformNormalForm.cleared_sandwich S A point edge hT
  have he : 4 * Nat.card Λ * m0 = (2 * Nat.card Λ) * (2*m0) := by
    calc
      _ = (2*2) * Nat.card Λ * m0 := rfl
      _ = _ := by ac_rfl
  rw [he,Function.iterate_mul,hclear]
  exact PositiveOutside.sandwich_iterate_full (S := S) H primitive point edge L R (by simpa only [Bool.decide_eq_true] using hpos) m0 hm0 hi hj D hD

include point edge in
/-- The global finite-source loop-palette maximum gives one uniform bound
for every nonempty input of the same actual return operation. -/
theorem uniform_return_iterate_full_global [Finite Λ]
    (H : HomogeneousSource S G) (primitive : SortwisePrimitive S)
    {i j : ι} {T : S.Menu i j → S.Menu i j} {g : Λ} {eps : Bool}
    (hT : UniformNormalForm S A T g eps true) (D : S.Menu i j) (hD : D.Nonempty) :
    T^[4 * Nat.card Λ * maxLoopPalette S] D = Set.univ :=
  uniform_return_iterate_full S A point edge H primitive hT (maxLoopPalette S)
    (maxLoopPalette_positive S) (loopPalette_card_le_max S i) (loopPalette_card_le_max S j) D hD

/-- A concrete pointwise normal form induces a genuine PARAMETRIC operation
on every parallel input, agreeing with the given path at its original seed. -/
theorem NormalForm.uniform {i j k l : ι} {D : S.Menu i j} {E : S.Menu k l} {p : Bool}
    (h : NormalForm S A ⟨i,j,D⟩ ⟨k,l,E⟩ p) :
    ∃ (T : S.Menu i j → S.Menu k l) (g : Λ) (eps : Bool),
      UniformNormalForm S A T g eps p ∧ T D = E := by
  cases h with
  | forward g C hc L R =>
    have ha : _ = A.tag g i := (congrArg Sigma.fst hc).symm.trans (A.source g ⟨i,j,D⟩)
    have hb : _ = A.tag g j := (congrArg (fun F : TaggedMenu S => F.2.1) hc).symm.trans
      (A.target g ⟨i,j,D⟩)
    cases ha; cases hb
    have hC : A.menuAct g D = C := by
      have he := (A.tagged_menuAct g D).trans hc
      simpa using he
    let T := fun F : S.Menu i j => L.left (PositiveOutside.right (A.menuAct g F) R)
    refine ⟨T,g,false,?_,?_⟩
    · exact .forward g (fun F => A.menuAct g F) (fun F => (A.tagged_menuAct g F).symm)
        L R (fun _ => rfl)
    · dsimp only [T]
      rw [hC]
  | reverse g C hc L R =>
    have ha : _ = A.tag g i := (congrArg Sigma.fst hc).symm.trans (A.source g ⟨i,j,D⟩)
    have hb : _ = A.tag g j := (congrArg (fun F : TaggedMenu S => F.2.1) hc).symm.trans
      (A.target g ⟨i,j,D⟩)
    cases ha; cases hb
    have hC : A.menuAct g D = C := by
      have he := (A.tagged_menuAct g D).trans hc
      simpa using he
    let T := fun F : S.Menu i j => L.left (PositiveOutside.right (S.opposite (A.menuAct g F)) R)
    refine ⟨T,g,true,?_,?_⟩
    · exact .reverse g (fun F => A.menuAct g F) (fun F => (A.tagged_menuAct g F).symm)
        L R (fun _ => rfl)
    · dsimp only [T]
      rw [hC]

include point edge in
/-- A syntactic positive closed path supplies ONE return operator, fixing its
seed, whose SAME bounded iterate fills EVERY nonempty parallel raw input. -/
theorem positive_return_uniform_bound [Finite Λ]
    (H : HomogeneousSource S G) (primitive : SortwisePrimitive S) {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    {i j : ι} (D : S.Menu i j)
    (hpath : PositiveGenerated S A Q ⟨i,j,D⟩ ⟨i,j,D⟩ true) :
    ∃ (T : S.Menu i j → S.Menu i j) (g : Λ) (eps : Bool),
      UniformNormalForm S A T g eps true ∧ T D = D ∧
      ∀ E : S.Menu i j, E.Nonempty → T^[4 * Nat.card Λ * maxLoopPalette S] E = Set.univ := by
  obtain ⟨T,g,eps,hT,hfixed⟩ := NormalForm.uniform S A
    (positiveGenerated_normalForm S A point edge hne hpath)
  exact ⟨T,g,eps,hT,hfixed,uniform_return_iterate_full_global S A point edge H primitive hT⟩

include point edge in
/-- Actual positive closed generation paths cannot pass through a proper
nonempty menu. The actual source assumptions discharge the cycle provider. -/
theorem positiveGenerated_closed_full [Finite Λ]
    (H : HomogeneousSource S G) (primitive : SortwisePrimitive S)
    {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    (D : TaggedMenu S) (hD : NonemptyMenu S D)
    (hpath : PositiveGenerated S A Q D D true) : Full S D := by
  rcases D with ⟨i,j,D⟩
  obtain ⟨T,g,eps,hT,hfixed,hfill⟩ := positive_return_uniform_bound S A point edge H primitive hne D hpath
  have hfull := hfill D hD
  have hiter : ∀ n, T^[n] D = D := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,hfixed]
  exact (hiter _).symm.trans hfull

end CCO.SafeReadings
