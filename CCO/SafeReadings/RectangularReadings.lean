import CCO.SafeReadings.BilateralReadings
import CCO.SafeReadings.BilateralRefinement

universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (E : EndpointGauge S A K)
variable (h : HereditarySelector S) (hCov : h.Covariant S A)
include hCov

/-- R07: bilateral support alone suffices for two independent readings;
the third menu is explicitly refined to a nonempty original PC menu. -/
theorem reading_bilateral (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (g k : K) {i j l : ι} (D : S.Menu i j) (F : S.Menu j l) (P : S.Menu i l)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hDF : D ⊆ S.product P (S.opposite F)) (hFD : F ⊆ S.product (S.opposite D) P) :
    ∃ c ∈ P, S.Triangle (reading E h g D hD) (reading E h k F hF) c := by
  obtain ⟨he,hpc⟩ := bilateral_refinement S C hPoint hEdge hD hF hP hDF hFD
  obtain ⟨c,hc,ht⟩ := reading_pair_supported E h hCov g k D F (P ∩ S.product D F) hD hF he hpc
  exact ⟨c,hc.1,ht⟩

/-- Every independent reading of the first menu survives the restriction
induced by the selected third atom. -/
theorem reading_mem_restrictLeft (hConv : LiteralConverse S A) (C : ExactCalculus S)
    (g k : K) {i j l : ι} (D : S.Menu i j) (F : S.Menu j l) (P : S.Menu i l)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hpc : S.PC D F P) :
    reading E h g D hD ∈ restrictLeft S D F (reading E h k P hP) := by
  obtain ⟨b,hb,ht⟩ := reading_pair_supported E h hCov g k (S.opposite D) P F
    (C.opposite hD) hP hF ((S.pc_rotate_output_second D F P).mp hpc)
  rw [reading_converse E h hCov hConv g D hD (C.opposite hD)] at ht
  refine ⟨reading_member E h g D hD,reading E h k P hP,by simp,S.conv b,S.mem_opposite hb,?_⟩
  simpa only [S.conv_invol] using S.triangle_cycle ht

/-- The other rotated restriction retains its own reading independently. -/
theorem reading_mem_restrictRight (hConv : LiteralConverse S A) (C : ExactCalculus S)
    (g k : K) {i j l : ι} (D : S.Menu i j) (F : S.Menu j l) (P : S.Menu i l)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hpc : S.PC D F P) :
    reading E h g F hF ∈ restrictRight S D F (reading E h k P hP) := by
  obtain ⟨a,ha,ht⟩ := reading_pair_supported E h hCov k g P (S.opposite F) D
    hP (C.opposite hF) hD ((S.pc_rotate_output_first D F P).mp hpc)
  rw [reading_converse E h hCov hConv g F hF (C.opposite hF)] at ht
  refine ⟨reading_member E h g F hF,S.conv a,S.mem_opposite ha,reading E h k P hP,by simp,?_⟩
  simpa only [S.conv_invol] using S.triangle_rotate (S.triangle_cycle (S.triangle_rotate_back ht))

/-- R08's specific chosen atoms survive BOTH original exact restrictions;
the two support inclusions and individual hereditary equalities are explicit. -/
theorem reading_restrictions (hConv : LiteralConverse S A) (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (g k l : K) {i j m : ι} (D : S.Menu i j) (F : S.Menu j m) (P : S.Menu i m)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hpc : S.PC D F P) :
    let c := reading E h l P hP
    let D' := restrictLeft S D F c
    let F' := restrictRight S D F c
    ∃ (heD : StrongExact.Exact S D') (heF : StrongExact.Exact S F'),
      reading E h g D hD ∈ D' ∧ reading E h k F hF ∈ F' ∧
      D' ⊆ S.product {c} (S.opposite F') ∧ F' ⊆ S.product (S.opposite D') {c} ∧
      reading E h g D' heD = reading E h g D hD ∧ reading E h k F' heF = reading E h k F hF := by
  dsimp only
  let c := reading E h l P hP
  let D' := restrictLeft S D F c
  let F' := restrictRight S D F c
  have ha : reading E h g D hD ∈ D' := reading_mem_restrictLeft E h hCov hConv C g l D F P hD hF hP hpc
  have hb : reading E h k F hF ∈ F' := reading_mem_restrictRight E h hCov hConv C k l D F P hD hF hP hpc
  have hnD : D'.Nonempty := ⟨_,ha⟩
  have hnF : F'.Nonempty := ⟨_,hb⟩
  have heD : StrongExact.Exact S D' := StrongExact.exact_inter S hD
    (C.product (StrongExact.exact_singleton S c) (C.opposite hF)) hnD
  have heF : StrongExact.Exact S F' := StrongExact.exact_inter S hF
    (C.product (C.opposite hD) (StrongExact.exact_singleton S c)) hnF
  obtain ⟨hl,hr⟩ := restricted_pair_bilateral S C hPoint hEdge c hD hF hnD hnF
  exact ⟨heD,heF,ha,hb,hl,hr,
    reading_heredity E h g D D' hD heD (fun _ hx => hx.1) ha,
    reading_heredity E h k F F' hF heF (fun _ hx => hx.1) hb⟩

/-- R08: ALL three reading parameters are independent. No relation
between g, k and l, no safe palette and no countability premise occurs. -/
theorem rectangular_reading_triangle (hConv : LiteralConverse S A) (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (g k l : K) {i j m : ι} (D : S.Menu i j) (F : S.Menu j m) (P : S.Menu i m)
    (hD : StrongExact.Exact S D) (hF : StrongExact.Exact S F) (hP : StrongExact.Exact S P)
    (hpc : S.PC D F P) :
    S.Triangle (reading E h g D hD) (reading E h k F hF) (reading E h l P hP) := by
  let c := reading E h l P hP
  let D' := restrictLeft S D F c
  let F' := restrictRight S D F c
  have ha : reading E h g D hD ∈ D' := reading_mem_restrictLeft E h hCov hConv C g l D F P hD hF hP hpc
  have hb : reading E h k F hF ∈ F' := reading_mem_restrictRight E h hCov hConv C k l D F P hD hF hP hpc
  have hnD : D'.Nonempty := ⟨_,ha⟩
  have hnF : F'.Nonempty := ⟨_,hb⟩
  have heD : StrongExact.Exact S D' := StrongExact.exact_inter S hD
    (C.product (StrongExact.exact_singleton S c) (C.opposite hF)) hnD
  have heF : StrongExact.Exact S F' := StrongExact.exact_inter S hF
    (C.product (C.opposite hD) (StrongExact.exact_singleton S c)) hnF
  obtain ⟨hl,hr⟩ := restricted_pair_bilateral S C hPoint hEdge c hD hF hnD hnF
  obtain ⟨c',hc',ht⟩ := reading_bilateral E h hCov C hPoint hEdge g k D' F' {c}
    heD heF (StrongExact.exact_singleton S c) hl hr
  have hec : c' = c := hc'
  rw [hec,reading_heredity E h g D D' hD heD (fun _ hx => hx.1) ha,
    reading_heredity E h k F F' hF heF (fun _ hx => hx.1) hb] at ht
  exact ht

end CCO.SafeReadings
