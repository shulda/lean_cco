import CCO.RealHull.Geometry.Separator

/-! Rectangle and folding are actual shared-edge amalgam calculations.
The prescribed different colours keep the free apexes distinct without SAP. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

theorem rectangle (H : HomogeneousSource S G) (p u v : Atom S) (hne : u ≠ v) :
    (row S p u ∩ row S p v).Nonempty ↔ (square S p ∩ row S u v).Nonempty := by
  constructor
  · rintro ⟨d,hdu,hdv⟩
    obtain ⟨x,y,z,hxy,hyz,hxz⟩ := (mem_row S p u d).mp hdu
    obtain ⟨y',hxy',hy'z⟩ := triangle_over_pair S H ((mem_row S p v d).mp hdv) hxz
    have hyy : y ≠ y' := by
      intro he
      exact hne (Option.some.inj (hyz.symm.trans ((congrArg (fun a => col S a z) he).trans hy'z)))
    obtain ⟨e,he⟩ := col_some_of_ne S hyy
    refine ⟨e,?_,?_⟩
    · exact (mem_row S p p e).mpr ⟨y,x,y',(col_symm S y x).trans hxy,hxy',he⟩
    · exact (mem_row S u v e).mpr ⟨y,z,y',hyz,(col_symm S z y').trans hy'z,he⟩
  · rintro ⟨e,hep,heuv⟩
    obtain ⟨l,r,hlr⟩ := S.realized e
    obtain ⟨x,hlx,hxr⟩ := triangle_over_pair S H ((mem_row S p p e).mp hep) hlr
    obtain ⟨z,hlz,hzr⟩ := triangle_over_pair S H ((mem_row S u v e).mp heuv) hlr
    have hxz : x ≠ z := by
      intro he
      have hpu : p = u := Option.some.inj (hlx.symm.trans ((congrArg (col S l) he).trans hlz))
      have hpv : p = v := Option.some.inj (hxr.symm.trans ((congrArg (fun a => col S a r) he).trans hzr))
      exact hne (hpu.symm.trans hpv)
    obtain ⟨d,hd⟩ := col_some_of_ne S hxz
    refine ⟨d,?_,?_⟩
    · exact (mem_row S p u d).mpr ⟨x,l,z,(col_symm S x l).trans hlx,hlz,hd⟩
    · exact (mem_row S p v d).mpr ⟨x,r,z,hxr,(col_symm S r z).trans hzr,hd⟩

theorem supportOrbit_off_diagonal (R : Support S) {u v : Atom S} (hne : u ≠ v) :
    SupportOrbit S R u v ↔ (R.val ∩ row S u v).Nonempty := by
  constructor
  · rintro ⟨x,y,z,hR,hu,hv⟩
    have hxy : x ≠ y := by
      rintro rfl
      exact hne (Option.some.inj ((Set.mem_singleton_iff.mp hu).symm.trans hv))
    obtain ⟨s,hs⟩ := col_some_of_ne S hxy
    refine ⟨s,(some_mem_plus S _ _).mp (hs ▸ hR),?_⟩
    exact (mem_row S u v s).mpr ⟨y,z,x,Set.mem_singleton_iff.mp hu,
      (col_symm S z x).trans hv,(col_symm S y x).trans hs⟩
  · rintro ⟨s,hs,htri⟩
    obtain ⟨x,y,z,hxy,hyz,hxz⟩ := (mem_row S u v s).mp htri
    exact ⟨z,x,y,((col_symm S z x).trans hxz).symm ▸ (some_mem_plus S _ _).mpr hs,
      hxy,(col_symm S z y).trans hyz⟩

theorem orbit_folding (H : HomogeneousSource S G) (R : Support S)
    (u v t : Atom S) (huv : SupportOrbit S R u v)
    (ht : t ∈ row S u v) (htR : t ∉ R.val) :
    ∃ t' ∈ square S u, t' ∉ R.val ∧ SupportOrbit S R t' t := by
  by_cases he : u = v
  · subst v
    exact ⟨t,ht,htR,supportOrbit_refl S R t⟩
  obtain ⟨s,hsR,hs⟩ := (supportOrbit_off_diagonal S R he).mp huv
  obtain ⟨x,z,hxz⟩ := S.realized v
  obtain ⟨y,hxy,hyz⟩ := triangle_over_pair S H (triangle_swap_first S ((mem_row S u v t).mp ht)) hxz
  obtain ⟨z',hxz',hz'z⟩ := triangle_over_pair S H (triangle_swap_first S ((mem_row S u v s).mp hs)) hxz
  have hyz' : y ≠ z' := by
    intro h
    have heq : t = s := Option.some.inj (hyz.symm.trans ((congrArg (fun a => col S a z) h).trans hz'z))
    exact htR (heq ▸ hsR)
  obtain ⟨t',htt'⟩ := col_some_of_ne S hyz'
  have ht'u : t' ∈ square S u :=
    (mem_row S u u t').mpr ⟨y,x,z',(col_symm S y x).trans hxy,hxz',htt'⟩
  have ht'R : t' ∉ R.val := by
    intro hR
    have hp : some t ∈ prod S (plus S R.val) (plus S R.val) :=
      ⟨y,z',z,htt'.symm ▸ (some_mem_plus S _ _).mpr hR,
        hz'z.symm ▸ (some_mem_plus S _ _).mpr hsR,hyz⟩
    exact htR ((some_mem_plus S _ _).mp (R.property hp))
  have horb : SupportOrbit S R t t' :=
    ⟨z',z,y,hz'z.symm ▸ (some_mem_plus S _ _).mpr hsR,
      (col_symm S z y).trans hyz,(col_symm S z' y).trans htt'⟩
  exact ⟨t',ht'u,ht'R,supportOrbit_symm S R horb⟩

end CCO.RealHull.Geometry
