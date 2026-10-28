import CCO.SIR.Positive.Direct.Consumers

namespace CCO.SIR.Positive.Direct

/-- Direct-model C24 on the LITERAL real carrier. Every particular old
finite induced isomorphism fixing C extends while all real parameters in
B∪C are fixed individually. The given map, including its values on the
whole base, is retained verbatim. -/
theorem prescribed_map_stationarity (A A' B C : Finset Point)
    (f : ↥(A ∪ C) ≃ ↥(A' ∪ C))
    (hcol : ∀ x y, colour x.val y.val = colour (f x).val (f y).val)
    (hfix : ∀ c (hc : c ∈ C),
      (f ⟨c,Finset.mem_union_right A hc⟩).val = c)
    (hA : Independent A C B) (hA' : Independent A' C B) :
    ∃ k : Aut, (∀ b ∈ B ∪ C, k • b = b) ∧
      ∀ x : ↥(A ∪ C), k • x.val = (f x).val := by
  classical
  obtain ⟨g,hgf⟩ := finite_extension (fun x : ↥(A ∪ C) => x.val)
    (fun x => (f x).val) hcol
  have hg : ∀ c ∈ C, g • c = c := fun c hc =>
    (hgf ⟨c,Finset.mem_union_right A hc⟩).trans (hfix c hc)
  have htransport : transport g (A ∪ C) = A' ∪ C := by
    ext x
    rw [mem_transport]
    constructor
    · rintro ⟨a,ha,hax⟩
      exact ((hgf ⟨a,ha⟩).symm.trans hax) ▸ (f ⟨a,ha⟩).property
    · intro hx
      let y : ↥(A' ∪ C) := ⟨x,hx⟩
      let a := f.symm y
      refine ⟨a.val,a.property,?_⟩
      exact (hgf a).trans (congrArg Subtype.val (f.apply_symm_apply y))
  have hleft (U : Finset Point) (hU : Independent U C B) : Independent (U ∪ C) C B :=
    independent_restriction (fun _ h => h) (fun _ hb => Finset.mem_union_left C hb)
      ((independent_normalization U B C).mpr hU)
  have htarget : Independent (transport g (A ∪ C)) C B := by
    rw [htransport]
    exact hleft A' hA'
  obtain ⟨k,hk,hkg⟩ := independent_stationarity (A ∪ C) B C g hg (hleft A hA) htarget
  exact ⟨k,hk,fun x => (hkg x.val x.property).trans (hgf x)⟩

end CCO.SIR.Positive.Direct
