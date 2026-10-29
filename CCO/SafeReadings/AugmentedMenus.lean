import CCO.SafeReadings.MenuCalculus
import CCO.SafeReadings.SafeTrace

/-! Evaluated menus, never chosen presentations. An original skeleton
need not be unique, and a safe trace need not be ORIGINAL exact. -/
universe u v w z t
namespace CCO.SafeReadings
open StrongExact Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def Augmented (safe : ∀ i j, S.Menu i j) {i j} (X : S.Menu i j) : Prop :=
  Exact S X ∨ ∃ D, Exact S D ∧ X = D ∩ safe i j ∧ X.Nonempty

def augmentedFamily (safe : ∀ i j, S.Menu i j) : Family S := {D | Augmented S safe D.2.2}

theorem Augmented.nonempty {safe : ∀ i j, S.Menu i j} {i j} {D : S.Menu i j}
    (hD : Augmented S safe D) : D.Nonempty := by
  rcases hD with h | ⟨_,_,_,h⟩
  · exact h.1
  · exact h

theorem Augmented.skeleton {safe : ∀ i j, S.Menu i j} {i j} {X : S.Menu i j}
    (hX : Augmented S safe X) : ∃ D, Exact S D ∧ (X = D ∨ X = D ∩ safe i j) := by
  rcases hX with h | ⟨D,hD,he,_⟩
  · exact ⟨X,h,Or.inl rfl⟩
  · exact ⟨D,hD,Or.inr he⟩

theorem Augmented.subset_skeleton {safe : ∀ i j, S.Menu i j} {i j} {X D : S.Menu i j}
    (he : X = D ∨ X = D ∩ safe i j) : X ⊆ D := by
  rcases he with rfl | rfl
  · exact fun _ h => h
  · exact Set.inter_subset_left

theorem Augmented.skeleton_product {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
    {i j k} {X D : S.Menu i j} {Y E : S.Menu j k}
    (hD : Exact S D) (hE : Exact S E) (hX : X.Nonempty) (hY : Y.Nonempty)
    (heX : X = D ∨ X = D ∩ safe i j) (heY : Y = E ∨ Y = E ∩ safe j k) :
    S.product X Y = S.product D E := by
  rcases heX with rfl | rfl
  · rcases heY with rfl | rfl
    · rfl
    · exact product_safe_trace S H sap hs _ hE hY
  · rw [safe_trace_product S H sap hs.amalgamation hD hX]
    rcases heY with rfl | rfl
    · rfl
    · exact product_safe_trace S H sap hs _ hE hY

theorem augmented_product_exact {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
    {i j k} {D : S.Menu i j} {E : S.Menu j k}
    (hD : Augmented S safe D) (hE : Augmented S safe E) : Exact S (S.product D E) := by
  obtain ⟨D',hD',heD⟩ := hD.skeleton
  obtain ⟨E',hE',heE⟩ := hE.skeleton
  rw [Augmented.skeleton_product S H sap hs hD' hE' hD.nonempty hE.nonempty heD heE]
  exact exact_product_of_SAP_CCO S H sap cco hD' hE'

theorem augmented_inter {safe : ∀ i j, S.Menu i j} {i j} {D E : S.Menu i j}
    (hD : Augmented S safe D) (hE : Augmented S safe E) (hne : (D ∩ E).Nonempty) :
    Augmented S safe (D ∩ E) := by
  obtain ⟨D',hD',heD⟩ := hD.skeleton
  obtain ⟨E',hE',heE⟩ := hE.skeleton
  have hne' : (D' ∩ E').Nonempty := by
    obtain ⟨a,ha,hb⟩ := hne
    exact ⟨a,Augmented.subset_skeleton S heD ha,Augmented.subset_skeleton S heE hb⟩
  have hex := exact_inter S hD' hE' hne'
  rcases heD with hd | hd <;> rcases heE with he | he
  · rw [hd,he]; exact Or.inl hex
  · refine Or.inr ⟨D' ∩ E',hex,?_,hne⟩
    rw [hd,he]; ext a; simp only [Set.mem_inter_iff]; tauto
  · refine Or.inr ⟨D' ∩ E',hex,?_,hne⟩
    rw [hd,he]; ext a; simp only [Set.mem_inter_iff]; tauto
  · refine Or.inr ⟨D' ∩ E',hex,?_,hne⟩
    rw [hd,he]; ext a; simp only [Set.mem_inter_iff]; tauto

theorem augmented_opposite {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
    {i j} {D : S.Menu i j} (hD : Augmented S safe D) : Augmented S safe (S.opposite D) := by
  rcases hD with h | ⟨E,hE,rfl,hne⟩
  · exact Or.inl (exact_opposite_of_gluing S (S.realEdgeGluing_of_SAP H sap) h)
  · refine Or.inr ⟨S.opposite E,exact_opposite_of_gluing S (S.realEdgeGluing_of_SAP H sap) hE,?_,?_⟩
    · rw [opposite_inter,hs.opposite]
    · obtain ⟨a,ha⟩ := hne
      exact ⟨S.conv a,S.mem_opposite ha⟩

end CCO.SafeReadings
