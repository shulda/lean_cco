import CCO.CloneTupleGeometry.TypedExact

/-! Finite indexed form of the independent typed exact-domain theorem.
Its source assumptions are only actual homogeneous SAP+HOM CCO, and the
two evaluated meets are nonempty. No clone or terminal source is imported. -/

universe u v w p q
namespace CCO.CloneTupleGeometry
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

private theorem indexed_presentation {i j : ι} {I : Type p} [Fintype I]
    (A : I → S.Menu i j) (words : I → List (PositiveWord S i j))
    (hw : ∀ a, A a = StrongExact.present S (words a)) :
    StrongExact.present S
      (StrongExact.flattenedPresentations S (Finset.univ.toList.map words)) =
      {c | ∀ a, c ∈ A a} := by
  classical
  ext c
  constructor
  · intro hc a
    rw [hw a]
    intro w hwa
    exact hc w (List.mem_flatMap.mpr
      ⟨words a,List.mem_map.mpr ⟨a,by simp,rfl⟩,hwa⟩)
  · intro hc w hwmem
    obtain ⟨ws,hws,hmemw⟩ := List.mem_flatMap.mp hwmem
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hws
    have hp : c ∈ StrongExact.present S (words a) := (hw a) ▸ hc a
    exact hp w hmemw

include H sap cco

/-- The independent selected distributivity theorem for arbitrary finite
families, including empty index types when their actual meets are nonempty. -/
theorem original_typed_exact_finite_double_meet
    {i j k : ι} {I : Type p} {J : Type q} [Finite I] [Finite J]
    (A : I → S.Menu i j) (B : J → S.Menu j k)
    (hA : ∀ a, StrongExact.Exact S (A a))
    (hB : ∀ b, StrongExact.Exact S (B b))
    (hLeft : ({c | ∀ a, c ∈ A a} : S.Menu i j).Nonempty)
    (hRight : ({c | ∀ b, c ∈ B b} : S.Menu j k).Nonempty) :
    S.product ({c | ∀ a, c ∈ A a} : S.Menu i j)
      ({c | ∀ b, c ∈ B b} : S.Menu j k) =
      {c | ∀ a b, c ∈ S.product (A a) (B b)} := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype J := Fintype.ofFinite J
  choose aw haw using fun a => (hA a).2
  choose bw hbw using fun b => (hB b).2
  let lefts := Finset.univ.toList.map aw
  let rights := Finset.univ.toList.map bw
  have hL := indexed_presentation S A aw haw
  have hR := indexed_presentation S B bw hbw
  have hLeft' : (StrongExact.present S (StrongExact.flattenedPresentations S lefts)).Nonempty := by
    change (StrongExact.present S
      (StrongExact.flattenedPresentations S (Finset.univ.toList.map aw))).Nonempty
    rw [hL]
    exact hLeft
  have hRight' : (StrongExact.present S (StrongExact.flattenedPresentations S rights)).Nonempty := by
    change (StrongExact.present S
      (StrongExact.flattenedPresentations S (Finset.univ.toList.map bw))).Nonempty
    rw [hR]
    exact hRight
  rw [← hL,← hR,original_typed_exact_double_meet S H sap cco lefts rights hLeft' hRight']
  ext c
  constructor
  · intro hc a b
    have h := hc (aw a) (List.mem_map.mpr ⟨a,by simp,rfl⟩)
      (bw b) (List.mem_map.mpr ⟨b,by simp,rfl⟩)
    simpa only [← haw a,← hbw b] using h
  · intro hc ws hws vs hvs
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hws
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hvs
    simpa only [← haw a,← hbw b] using hc a b

/-- One fixed exact left factor and one arbitrary finite nonempty exact
meet. This retains the actual evaluated-meet nonemptiness guard. -/
theorem original_typed_exact_finite_right_meet
    {i j k : ι} {J : Type q} [Finite J]
    (A : S.Menu i j) (B : J → S.Menu j k)
    (hA : StrongExact.Exact S A) (hB : ∀ b, StrongExact.Exact S (B b))
    (hRight : ({c | ∀ b, c ∈ B b} : S.Menu j k).Nonempty) :
    S.product A ({c | ∀ b, c ∈ B b} : S.Menu j k) =
      {c | ∀ b, c ∈ S.product A (B b)} := by
  have hunit : ({c | ∀ _ : Unit, c ∈ A} : S.Menu i j) = A := by
    ext c
    simp
  have hn : ({c | ∀ _ : Unit, c ∈ A} : S.Menu i j).Nonempty := by
    rw [hunit]
    exact hA.1
  have he := original_typed_exact_finite_double_meet S H sap cco
    (fun _ : Unit => A) B (fun _ => hA) hB hn hRight
  simpa [hunit] using he

/-- The finite left-meet counterpart, with the same explicit guard. -/
theorem original_typed_exact_finite_left_meet
    {i j k : ι} {I : Type p} [Finite I]
    (A : I → S.Menu i j) (B : S.Menu j k)
    (hA : ∀ a, StrongExact.Exact S (A a)) (hB : StrongExact.Exact S B)
    (hLeft : ({c | ∀ a, c ∈ A a} : S.Menu i j).Nonempty) :
    S.product ({c | ∀ a, c ∈ A a} : S.Menu i j) B =
      {c | ∀ a, c ∈ S.product (A a) B} := by
  have hunit : ({c | ∀ _ : Unit, c ∈ B} : S.Menu j k) = B := by
    ext c
    simp
  have hn : ({c | ∀ _ : Unit, c ∈ B} : S.Menu j k).Nonempty := by
    rw [hunit]
    exact hB.1
  have he := original_typed_exact_finite_double_meet S H sap cco
    A (fun _ : Unit => B) hA (fun _ => hB) hLeft hn
  simpa [hunit] using he

end
end CCO.CloneTupleGeometry
