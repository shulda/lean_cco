import CCO.StrongExact.SourceExactCalculus

/-! B047 C01–C03. Nonempty STRONG exact saturation distributes over a
finite exact meet. All relations below are diversity palettes, never RAW. -/

universe u v w
namespace CCO.PairSafeSplit
open StrongExact
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

private def presentations (Ds : List (S.Menu i j))
    (hD : ∀ D ∈ Ds, Exact S D) : List (List (PositiveWord S i j)) :=
  Ds.attach.map (fun D => Classical.choose (hD D.val D.property).2)

private theorem presentations_meet (Ds : List (S.Menu i j))
    (hD : ∀ D ∈ Ds, Exact S D) :
    present S (flattenedPresentations S (presentations S Ds hD)) = meetMenus S Ds := by
  classical
  ext a
  constructor
  · intro h D hDmem
    have eq := Classical.choose_spec (hD D hDmem).2
    rw [eq]
    intro word hw
    apply h word
    exact List.mem_flatMap.mpr ⟨_,List.mem_map.mpr
      ⟨⟨D,hDmem⟩,List.mem_attach _ _,rfl⟩,hw⟩
  · intro h word hw
    obtain ⟨p,hp,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hp
    have hh := h D.val D.property
    rw [Classical.choose_spec (hD D.val D.property).2] at hh
    exact hh word hw

private theorem meet_exact (Ds : List (S.Menu i j))
    (hD : ∀ D ∈ Ds, Exact S D) (hne : (meetMenus S Ds).Nonempty) :
    Exact S (meetMenus S Ds) :=
  ⟨hne,⟨flattenedPresentations S (presentations S Ds hD),(presentations_meet S Ds hD).symm⟩⟩

variable {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S)
include H sap cco

theorem product_meet_left (A : S.Menu i j) (Ds : List (S.Menu j k))
    (hA : Exact S A) (hD : ∀ D ∈ Ds, Exact S D) (hne : (meetMenus S Ds).Nonempty) :
    S.product A (meetMenus S Ds) = {c | ∀ D ∈ Ds, c ∈ S.product A D} := by
  classical
  obtain ⟨ha,words,hwords⟩ := hA
  have base := product_distrib_right_exact_of_SAP_CCO S H sap cco words
    (presentations S Ds hD) (hwords ▸ ha) (by rw [presentations_meet]; exact hne)
  rw [← hwords,presentations_meet] at base
  rw [base]
  ext c
  constructor
  · intro h D hDmem
    have hp := h _ (List.mem_map.mpr ⟨⟨D,hDmem⟩,List.mem_attach _ _,rfl⟩)
    rwa [← Classical.choose_spec (hD D hDmem).2] at hp
  · intro h p hp
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hp
    rw [← Classical.choose_spec (hD D.val D.property).2]
    exact h D.val D.property

theorem product_meet_right (Ds : List (S.Menu i j)) (A : S.Menu j k)
    (hD : ∀ D ∈ Ds, Exact S D) (hA : Exact S A) (hne : (meetMenus S Ds).Nonempty) :
    S.product (meetMenus S Ds) A = {c | ∀ D ∈ Ds, c ∈ S.product D A} := by
  classical
  obtain ⟨ha,words,hwords⟩ := hA
  have base := product_distrib_left_exact_of_SAP_CCO S H sap cco
    (presentations S Ds hD) words (by rw [presentations_meet]; exact hne) (hwords ▸ ha)
  rw [← hwords,presentations_meet] at base
  rw [base]
  ext c
  constructor
  · intro h D hDmem
    have hp := h _ (List.mem_map.mpr ⟨⟨D,hDmem⟩,List.mem_attach _ _,rfl⟩)
    rwa [← Classical.choose_spec (hD D hDmem).2] at hp
  · intro h p hp
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hp
    rw [← Classical.choose_spec (hD D.val D.property).2]
    exact h D.val D.property

/-- Source lem:exact-saturation-intersection. The common meet must be
NONEMPTY; this theorem supplies no RAW identity or empty-meet extension. -/
theorem strong_exact_saturation_intersection (Ka : S.Menu i i) (Kb : S.Menu j j)
    (Ds : List (S.Menu i j)) (hKa : Exact S Ka) (hKb : Exact S Kb)
    (hD : ∀ D ∈ Ds, Exact S D) (hne : (meetMenus S Ds).Nonempty) :
    S.product (S.product Ka (meetMenus S Ds)) Kb =
      {c | ∀ D ∈ Ds, c ∈ S.product (S.product Ka D) Kb} := by
  classical
  let lefts := Ds.map (S.product Ka)
  have hx : ∀ D ∈ lefts, Exact S D := by
    intro D h
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
    exact exact_product_of_SAP_CCO S H sap cco hKa (hD d hd)
  have he : meetMenus S lefts = S.product Ka (meetMenus S Ds) := by
    rw [product_meet_left S H sap cco Ka Ds hKa hD hne]
    ext c
    simp only [lefts,meetMenus,List.mem_map,forall_exists_index,and_imp,
      forall_apply_eq_imp_iff₂,Set.mem_setOf_eq]
  have hn : (meetMenus S lefts).Nonempty := by
    rw [he]
    exact (exact_product_of_SAP_CCO S H sap cco hKa (meet_exact S Ds hD hne)).1
  rw [← he,product_meet_right S H sap cco lefts Kb hx hKb hn]
  ext c
  simp only [lefts,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂,Set.mem_setOf_eq]

end
end CCO.PairSafeSplit
