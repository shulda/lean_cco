import CCO.SafeReadings.SafeTrace

/-! Finite safe padding inside the original native source. Empty-base strong
safe amalgamation adds one point at a time; homogeneity moves the entire old
factor back to its literal original points. No completion or EPPA is used. -/

universe u v w t
namespace CCO.RelativeMI
open SafeReadings

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Γ : Type t} [Group Γ] [MulAction Γ (Sigma X)]

private theorem safePair_of_taggedColour_eq
    {safe : ∀ i j, S.Menu i j} {p q p' q' : Sigma X}
    (h : taggedColour S p q = taggedColour S p' q')
    (hpq : SafePair S safe p q) : SafePair S safe p' q' := by
  obtain ⟨i,x⟩ := p
  obtain ⟨j,y⟩ := q
  obtain ⟨i',x'⟩ := p'
  obtain ⟨j',y'⟩ := q'
  have hi : i = i' := congrArg Sigma.fst h
  have hj : j = j' := congrArg (fun c => c.2.1) h
  subst i'
  subst j'
  have hc : S.colour x y = S.colour x' y' := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  obtain ⟨a,ha,haxy⟩ := hpq
  exact ⟨a,ha,hc.symm.trans haxy⟩

private theorem safePair_reverse {safe : ∀ i j, S.Menu i j}
    (hs : SafeSystem S safe) {p q : Sigma X}
    (hpq : SafePair S safe p q) : SafePair S safe q p := by
  obtain ⟨a,ha,hcol⟩ := hpq
  refine ⟨S.conv a,?_,(S.colour_swap p.2 q.2 a).mp hcol⟩
  rw [← hs.opposite]
  exact S.mem_opposite ha

/-- Add one genuinely fresh native point of the requested owner sort, safe
in both directions to every point of the literal old finite set. -/
theorem native_safe_add_one (H : HomogeneousSource S Γ)
    (safe : ∀ i j, S.Menu i j) (hs : SafeSystem S safe)
    (A : Finset (Sigma X)) (i : ι) :
    ∃ p : Sigma X, p ∉ A ∧ p.1 = i ∧
      ∀ q ∈ A, SafePair S safe q p ∧ SafePair S safe p q := by
  classical
  let C : FiniteInduced (X := X) := ⟨∅,Set.finite_empty⟩
  let L : FiniteInduced (X := X) := FiniteInduced.ofFinset A
  let x : X i := (S.nonemptySort i).some
  let B : FiniteInduced (X := X) := ⟨{⟨i,x⟩},Set.finite_singleton _⟩
  let eCL := inducedInclusion S C L (Set.empty_subset _)
  let eCB := inducedInclusion S C B (Set.empty_subset _)
  obtain ⟨D,eL,eB,_,hsep,hsafe⟩ := hs.amalgamation.amalgamate C L B eCL eCB
  obtain ⟨g,hg⟩ := H.extends_partial_iso L D eL
  let b : ↥B.vertices := ⟨⟨i,x⟩,Set.mem_singleton _⟩
  let p : Sigma X := g⁻¹ • (eB.toEmbedding b).val
  have hold (a : ↥L.vertices) : g⁻¹ • (eL.toEmbedding a).val = a.val := by
    rw [← hg a]
    simp
  have hp : p ∉ A := by
    intro hpA
    let a : ↥L.vertices := ⟨p,hpA⟩
    have he : eL.toEmbedding a = eB.toEmbedding b := by
      apply Subtype.ext
      rw [← hg a]
      change g • (g⁻¹ • (eB.toEmbedding b).val) = _
      simp
    obtain ⟨c,_,_⟩ := hsep a b he
    exact Set.notMem_empty _ c.property
  have hsort : p.1 = i :=
    (H.preserves_sort g⁻¹ (eB.toEmbedding b).val).trans (eB.preserves_sort b)
  refine ⟨p,hp,hsort,?_⟩
  intro q hq
  let a : ↥L.vertices := ⟨q,hq⟩
  have hsafe : SafePair S safe (eL.toEmbedding a).val (eB.toEmbedding b).val :=
    hsafe a b (fun c => (Set.notMem_empty _ c.property).elim)
      (fun c => (Set.notMem_empty _ c.property).elim)
  have hqp : SafePair S safe q p := by
    have h := safePair_of_taggedColour_eq S
      (H.preserves_colours g⁻¹ (eL.toEmbedding a).val (eB.toEmbedding b).val).symm hsafe
    simpa only [hold a] using h
  exact ⟨hqp,safePair_reverse S hs hqp⟩

/-- Padding for any selected finite family of owner sorts. All old points
are retained literally; safety covers new--old and new--new pairs. -/
theorem native_safe_padding_on (H : HomogeneousSource S Γ)
    (safe : ∀ i j, S.Menu i j) (hs : SafeSystem S safe)
    (seed : Finset (Sigma X)) (owners : Finset ι) :
    ∃ E : Finset (Sigma X), seed ⊆ E ∧
      (∀ i ∈ owners, ∃ p ∈ E, p.1 = i) ∧
      (∀ a ∈ E, a ∉ seed → ∀ b ∈ E, a ≠ b → SafePair S safe a b) := by
  classical
  induction owners using Finset.induction_on with
  | empty =>
    refine ⟨seed,fun _ h => h,?_,?_⟩
    · intro i hi
      exact (Finset.notMem_empty i hi).elim
    · intro a ha hna
      exact (hna ha).elim
  | @insert i owners _ ih =>
    obtain ⟨E,hseed,howners,hsafe⟩ := ih
    obtain ⟨p,hp,hpi,hpSafe⟩ := native_safe_add_one S H safe hs E i
    refine ⟨insert p E,fun a ha => Finset.mem_insert_of_mem (hseed ha),?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨p,Finset.mem_insert_self _ _,hpi⟩
      · obtain ⟨q,hq,hqj⟩ := howners j hj
        exact ⟨q,Finset.mem_insert_of_mem hq,hqj⟩
    · intro a ha hna b hb hab
      rcases Finset.mem_insert.mp ha with haNew | haOld
      · rcases Finset.mem_insert.mp hb with hbNew | hbOld
        · exact (hab (haNew.trans hbNew.symm)).elim
        · rw [haNew]
          exact (hpSafe b hbOld).2
      · rcases Finset.mem_insert.mp hb with hbNew | hbOld
        · rw [hbNew]
          exact (hpSafe a haOld).1
        · exact hsafe a haOld hna b hbOld hab

/-- The finite native padding used by the relative MI construction. There
is one final actual finite set, retaining the literal seed, meeting every
owner, and safe on EVERY distinct ordered pair touching a new point. -/
theorem native_safe_padding (H : HomogeneousSource S Γ)
    (safe : ∀ i j, S.Menu i j) (hs : SafeSystem S safe)
    (seed : Finset (Sigma X)) :
    ∃ E : Finset (Sigma X), seed ⊆ E ∧
      (∀ i, ∃ p ∈ E, p.1 = i) ∧
      (∀ a ∈ E, a ∉ seed → ∀ b ∈ E, a ≠ b → SafePair S safe a b) := by
  let : Fintype ι := S.finiteSort
  obtain ⟨E,hseed,howners,hsafe⟩ := native_safe_padding_on S H safe hs seed Finset.univ
  exact ⟨E,hseed,fun i => howners i (Finset.mem_univ i),hsafe⟩

end CCO.RelativeMI
