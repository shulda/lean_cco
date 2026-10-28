import CCO.SIR.Positive.Basic
import CCO.SIR.Positive.FiniteMap

/-! Pointwise stationarity for EVERY prescribed old finite isomorphism.
The finite map itself is retained in the conclusion. -/
universe u v w t
namespace CCO.SIR.Positive

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [MulAction G (Sigma X)]
variable [DecidableEq (Sigma X)]

/-- A real SIR and actual old-source homogeneity extend any particular
finite induced map fixing C to an automorphism fixing B∪C pointwise,
provided both its displayed sides are independent from B over C. No
setwise replacement of the named parameters or prescribed map is used. -/
theorem StationaryIndependence.prescribed_map_stationarity
    {I : Finset (Sigma X) → Finset (Sigma X) → Finset (Sigma X) → Prop}
    (HI : StationaryIndependence (G := G) I) (H : HomogeneousSource S G)
    (A A' B C : Finset (Sigma X))
    (f : ↥(A ∪ C) ≃ ↥(A' ∪ C))
    (hcol : ∀ x y, taggedColour S x.val y.val =
      taggedColour S (f x).val (f y).val)
    (hfix : ∀ c (hc : c ∈ C),
      (f ⟨c, Finset.mem_union_right A hc⟩).val = c)
    (hA : I A C B) (hA' : I A' C B) :
    ∃ k : G, (∀ b ∈ B ∪ C, k • b = b) ∧
      ∀ x : ↥(A ∪ C), k • x.val = (f x).val := by
  classical
  obtain ⟨g,hg,hgf⟩ := extends_prescribed_map H A A' C f hcol hfix
  have htransport : transport g (A ∪ C) = A' ∪ C := by
    ext x
    rw [mem_transport]
    constructor
    · rintro ⟨a,ha,hax⟩
      have hf := (f ⟨a,ha⟩).property
      exact ((hgf ⟨a,ha⟩).symm.trans hax) ▸ hf
    · intro hx
      let y : ↥(A' ∪ C) := ⟨x,hx⟩
      let a := f.symm y
      refine ⟨a.val,a.property,?_⟩
      exact (hgf a).trans (congrArg Subtype.val (f.apply_symm_apply y))
  have hleft (U : Finset (Sigma X)) (hU : I U C B) : I (U ∪ C) C B := by
    have hh := (HI.normalization U B C).mpr hU
    exact HI.restriction (U ∪ C) (B ∪ C) C (U ∪ C) B
      (fun _ h => h) (fun _ hb => Finset.mem_union_left C hb) hh
  have htarget : I (transport g (A ∪ C)) C B := by
    rw [htransport]
    exact hleft A' hA'
  obtain ⟨k,hk,hkg⟩ := HI.stationarity (A ∪ C) B C g hg (hleft A hA) htarget
  exact ⟨k,hk,fun x => (hkg x.val x.property).trans (hgf x)⟩

end CCO.SIR.Positive
