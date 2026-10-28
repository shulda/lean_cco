import CCO.Selectors.Generated

/-! Parallel return transformations and their NR2 aperiodicity. -/
universe u v w t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

namespace Outside
variable {S}
theorem left_left_comm (edge : S.RealEdgeGluing)
    (L P : Outside S i i) (A : S.Menu i j) : L.left (P.left A) = P.left (L.left A) := by
  cases L <;> cases P <;> simp only [left]
  rw [←S.product_assoc_of_edge_gluing edge,←S.product_assoc_of_edge_gluing edge]
  rw [S.loop_product_commute]

theorem right_right_comm (edge : S.RealEdgeGluing)
    (R Q : Outside S j j) (A : S.Menu i j) :
    right (right A R) Q = right (right A Q) R := by
  cases R <;> cases Q <;> simp only [right]
  rw [S.product_assoc_of_edge_gluing edge,S.product_assoc_of_edge_gluing edge]
  rw [S.loop_product_commute]

theorem left_iterate (edge : S.RealEdgeGluing) (P : S.Menu i i)
    (n : Nat) (A : S.Menu i j) :
    (fun B : S.Menu i j => S.product P B)^[n+1] A = S.product (loopPower S P n) A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih,←S.product_assoc_of_edge_gluing edge]
    rfl

theorem right_iterate (edge : S.RealEdgeGluing) (P : S.Menu j j)
    (n : Nat) (A : S.Menu i j) :
    (fun B : S.Menu i j => S.product B P)^[n+1] A = S.product A (loopPower S P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,S.product_assoc_of_edge_gluing edge]
    rfl

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
theorem left_stable (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : FullNR2 S (G := G)) (L : Outside S i i) :
    ∃ N : Nat, ∀ n, N ≤ n →
      (fun A : S.Menu i j => L.left A)^[n] = (fun A : S.Menu i j => L.left A)^[n+1] := by
  cases L with
  | absent =>
    refine ⟨0,?_⟩
    intro n _
    change (id : S.Menu i j → S.Menu i j)^[n] = id^[n+1]
    simp only [Function.iterate_id]
  | present P hP =>
    obtain ⟨N,hN⟩ := loopPower_eventually_constant S H sap nr2 P hP.1
    refine ⟨N+1,?_⟩
    intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    funext A
    change (fun B : S.Menu i j => S.product P B)^[k+1] A =
      (fun B : S.Menu i j => S.product P B)^[k+1+1] A
    rw [left_iterate (S.realEdgeGluing_of_SAP H sap),left_iterate (S.realEdgeGluing_of_SAP H sap)]
    rw [hN k (by omega)]

theorem right_stable (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : FullNR2 S (G := G)) (R : Outside S j j) :
    ∃ N : Nat, ∀ n, N ≤ n →
      (fun A : S.Menu i j => right A R)^[n] = (fun A : S.Menu i j => right A R)^[n+1] := by
  cases R with
  | absent =>
    refine ⟨0,?_⟩
    intro n _
    change (id : S.Menu i j → S.Menu i j)^[n] = id^[n+1]
    simp only [Function.iterate_id]
  | present P hP =>
    obtain ⟨N,hN⟩ := loopPower_eventually_constant S H sap nr2 P hP.1
    refine ⟨N+1,?_⟩
    intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    funext A
    change (fun B : S.Menu i j => S.product B P)^[k+1] A =
      (fun B : S.Menu i j => S.product B P)^[k+1+1] A
    rw [right_iterate (S.realEdgeGluing_of_SAP H sap),right_iterate (S.realEdgeGluing_of_SAP H sap)]
    rw [hN k (by omega)]
end Outside

def returnMap (L : Outside S i i) (R : Outside S j j) (A : S.Menu i j) : S.Menu i j :=
  L.left (Outside.right A R)

theorem returnMap_commute (edge : S.RealEdgeGluing)
    (L P : Outside S i i) (R Q : Outside S j j) :
    Function.Commute (returnMap S L R) (returnMap S P Q) := by
  intro A
  unfold returnMap
  rw [←Outside.left_right edge,Outside.left_left_comm edge,
    Outside.right_right_comm edge,Outside.left_right edge]

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

theorem returnMap_eventually_stable (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : FullNR2 S (G := G)) (L : Outside S i i) (R : Outside S j j) :
    ∃ N : Nat, ∀ n, N ≤ n → (returnMap S L R)^[n] = (returnMap S L R)^[n+1] := by
  obtain ⟨l,hl⟩ := Outside.left_stable H sap nr2 (j := j) L
  obtain ⟨r,hr⟩ := Outside.right_stable H sap nr2 (i := i) R
  have hc : Function.Commute (fun A : S.Menu i j => L.left A)
      (fun A : S.Menu i j => Outside.right A R) := fun A =>
    Outside.left_right (S.realEdgeGluing_of_SAP H sap) L A R
  refine ⟨max l r,?_⟩
  intro n hn
  change ((fun A : S.Menu i j => L.left A) ∘ (fun A => Outside.right A R))^[n] =
    ((fun A : S.Menu i j => L.left A) ∘ (fun A => Outside.right A R))^[n+1]
  rw [hc.comp_iterate n,hc.comp_iterate (n+1),hl n (le_trans (le_max_left _ _) hn),
    hr n (le_trans (le_max_right _ _) hn)]

/-- Elementary commuting-return argument, applied below to actual loop actions. -/
theorem commuting_stable_return {T : Type*} (f g : T → T)
    (comm : Function.Commute f g) (N : Nat) (stable : f^[N] = f^[N+1])
    (a : T) (ha : g (f a) = a) : f a = a := by
  have hfix : ∀ n : Nat, (g ∘ f)^[n] a = a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,Function.comp_apply,ha,ih]
  have hN : g^[N] (f^[N] a) = a := by
    simpa only [comm.symm.comp_iterate,Function.comp_apply] using hfix N
  calc
    f a = f (g^[N] (f^[N] a)) := congrArg f hN.symm
    _ = g^[N] (f (f^[N] a)) := (comm.iterate_right N) _
    _ = g^[N] (f^[N+1] a) := by rw [Function.iterate_succ_apply']
    _ = g^[N] (f^[N] a) := by rw [←stable]
    _ = a := hN

/-- Original generated-family no-return under actual homogeneous SAP+NR2.
The exact calculus argument is supplied by the original source constructor. -/
theorem fullNoReturn_of_nr2 (alg : ExactCalculus S)
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : FullNR2 S (G := G)) :
    FullNoReturn S := by
  intro i j A B hA hB hf
  have edge : S.RealEdgeGluing := S.realEdgeGluing_of_SAP H sap
  obtain ⟨L,R,hT⟩ := parallel_return S alg edge
    (generated_normalForm S alg edge A ((hf ⟨i,j,B⟩).mpr (.seed)))
  obtain ⟨P,Q,hV⟩ := parallel_return S alg edge
    (generated_normalForm S alg edge B ((hf ⟨i,j,A⟩).mp (.seed)))
  obtain ⟨N,hN⟩ := returnMap_eventually_stable S H sap nr2 L R
  have hVT : returnMap S P Q (returnMap S L R A) = A := by
    change P.left (Outside.right (L.left (Outside.right A R)) Q) = A
    rw [←hT]
    exact hV.symm
  have hfix := commuting_stable_return (returnMap S L R) (returnMap S P Q)
    (returnMap_commute S edge L P R Q) N (hN N le_rfl) A hVT
  exact (hT.trans hfix).symm

end CCO.Selectors
