import CCO.SafeReadings.SafePathWitness
import CCO.StrongExact.SourceExactCalculus

/-! Arbitrary multipliers, rather than original-exact multipliers, are
essential when removing TWO evaluated safe traces successively. -/
universe u v w
namespace CCO.SafeReadings
open StrongExact
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]

structure SafeSystem (safe : ∀ i j, S.Menu i j) : Prop where
  nonempty : ∀ i j, (safe i j).Nonempty
  opposite : ∀ i j, S.opposite (safe i j) = safe j i
  amalgamation : StrongSafeAmalgamation S safe

theorem long_present_meets_safe (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j} (ws : List (PositiveWord S i j))
    (hlong : ∀ a, (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (hne : (present S ws).Nonempty) : (present S ws ∩ safe i j).Nonempty := by
  obtain ⟨d,hd⟩ := hne
  obtain ⟨x,y,hxy⟩ := S.realized d
  obtain ⟨U,hU,hx,hy,hZ,point,hinj,hkeep,a,ha,_⟩ :=
    long_presentation_safe_modification S H sap hs ws hlong d hd x y hxy ∅ Set.finite_empty
  exact ⟨a,ha⟩

theorem exact_nonsingleton_meets_safe (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j} {D : S.Menu i j} (hD : Exact S D) (hns : ∀ a, D ≠ {a}) :
    (D ∩ safe i j).Nonempty := by
  obtain ⟨ws,rfl,hlong⟩ := exact_nonsingleton_presentation_long S hD hns
  exact long_present_meets_safe S H sap hs ws hlong hD.1

theorem long_present_trace_product (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j k} (ws : List (PositiveWord S i j))
    (hlong : ∀ a, (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (E : S.Menu j k) :
    S.product (present S ws ∩ safe i j) E = S.product (present S ws) E := by
  apply Set.Subset.antisymm
  · exact S.product_mono Set.inter_subset_left (fun _ h => h)
  · rintro c ⟨d,hd,e,he,x,y,z,hxy,hyz,hxz⟩
    have hneXY := S.atomRel_ne hxy
    have hneYZ := S.atomRel_ne hyz
    have hneXZ := S.atomRel_ne hxz
    obtain ⟨U,hU,hx,hy,hZ,point,hinj,hkeep,a,ha,hacol⟩ :=
      long_presentation_safe_modification S H sap hs ws hlong d hd x y hxy
        {⟨k,z⟩} (Set.finite_singleton _)
    have hz : (⟨k,z⟩ : Sigma X) ∈ U := hZ (by simp)
    let px : U := ⟨⟨i,x⟩,hx⟩
    let py : U := ⟨⟨j,y⟩,hy⟩
    let pz : U := ⟨⟨k,z⟩,hz⟩
    have hyz' : S.colour (point py) (point pz) = some e :=
      (hkeep py pz (fun h => hneXY h.1.symm) (fun h => hneXZ h.2.symm)).trans hyz
    have hxz' : S.colour (point px) (point pz) = some c :=
      (hkeep px pz (fun h => hneYZ h.2.symm) (fun h => hneXY h.1)).trans hxz
    exact ⟨a,ha,e,he,point px,point py,point pz,hacol,hyz',hxz'⟩

/-- The multiplier is ANY actual menu; it need not be exact or traced.
Even its nonemptiness is unnecessary for the equality itself. -/
theorem safe_trace_product (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j k} {D : S.Menu i j} (hD : Exact S D)
    (htrace : (D ∩ safe i j).Nonempty) (E : S.Menu j k) :
    S.product (D ∩ safe i j) E = S.product D E := by
  classical
  by_cases hsingle : ∃ a, D = {a}
  · obtain ⟨a,rfl⟩ := hsingle
    have ha : a ∈ safe i j := by
      obtain ⟨b,hb,hs⟩ := htrace
      simpa only [Set.mem_singleton_iff.mp hb] using hs
    have he : ({a} : S.Menu i j) ∩ safe i j = {a} := by
      exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr ha)
    rw [he]
  · obtain ⟨ws,rfl,hlong⟩ := exact_nonsingleton_presentation_long S hD
      (fun a he => hsingle ⟨a,he⟩)
    exact long_present_trace_product S H sap hs ws hlong E

theorem opposite_inter {i j} (D E : S.Menu i j) :
    S.opposite (D ∩ E) = S.opposite D ∩ S.opposite E := rfl

theorem product_safe_trace (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
    {i j k} (D : S.Menu i j) {E : S.Menu j k} (hE : Exact S E)
    (htrace : (E ∩ safe j k).Nonempty) :
    S.product D (E ∩ safe j k) = S.product D E := by
  have hop : (S.opposite E ∩ safe k j).Nonempty := by
    obtain ⟨a,ha,hsafe⟩ := htrace
    exact ⟨S.conv a,S.mem_opposite ha,by rw [← hs.opposite]; exact S.mem_opposite hsafe⟩
  have he := safe_trace_product S H sap hs.amalgamation
    (exact_opposite_of_gluing S (S.realEdgeGluing_of_SAP H sap) hE) hop (S.opposite D)
  have hi : S.opposite E ∩ safe k j = S.opposite (E ∩ safe j k) := by
    rw [opposite_inter,hs.opposite]
  rw [hi,← S.product_opposite,← S.product_opposite] at he
  have he' := congrArg S.opposite he
  simpa only [S.opposite_opposite] using he'

end CCO.SafeReadings
