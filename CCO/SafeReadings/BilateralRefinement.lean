import CCO.SafeReadings.MenuCalculus

universe u v w
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

private theorem opposite_inter (A B : S.Menu i j) :
    S.opposite (A ∩ B) = S.opposite A ∩ S.opposite B := rfl

/-- Right multiplication distributes at an actual nonempty original meet. -/
theorem original_distrib_right (C : ExactCalculus S)
    {D E : S.Menu i j} {P : S.Menu j k}
    (hD : StrongExact.Exact S D) (hE : StrongExact.Exact S E)
    (hP : StrongExact.Exact S P) (hDE : (D ∩ E).Nonempty) :
    S.product (D ∩ E) P = S.product D P ∩ S.product E P := by
  have hne : (S.opposite D ∩ S.opposite E).Nonempty := by
    obtain ⟨a,ha,hb⟩ := hDE
    exact ⟨S.conv a,S.mem_opposite ha,S.mem_opposite hb⟩
  have h := C.distrib (C.opposite hP) (C.opposite hD) (C.opposite hE) hne
  have h' := congrArg S.opposite h
  simpa only [S.product_opposite,S.opposite_opposite,opposite_inter] using h'

/-- A bilateral original support pair admits the actual full PC refinement. -/
theorem bilateral_refinement (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (_hEdge : S.RealEdgeGluing)
    {D : S.Menu i j} {A : S.Menu j k} {P : S.Menu i k}
    (hD : StrongExact.Exact S D) (hA : StrongExact.Exact S A)
    (hP : StrongExact.Exact S P)
    (hDA : D ⊆ S.product P (S.opposite A))
    (hAD : A ⊆ S.product (S.opposite D) P) :
    StrongExact.Exact S (P ∩ S.product D A) ∧ S.PC D A (P ∩ S.product D A) := by
  have hne : (P ∩ S.product D A).Nonempty := by
    obtain ⟨d,hd⟩ := hD.1
    obtain ⟨p,hp,a,ha,htri⟩ := hDA hd
    exact ⟨p,hp,d,hd,S.conv a,ha,S.triangle_rotate htri⟩
  have hprod := C.product hD hA
  refine ⟨StrongExact.exact_inter S hP hprod hne,fun _ h => h.2,?_,?_⟩
  · intro d hd
    rw [original_distrib_right S C hP hprod (C.opposite hA) hne]
    refine ⟨hDA hd,?_⟩
    obtain ⟨a,ha⟩ := hA.1
    obtain ⟨p,htri⟩ := hPoint d a
    exact ⟨p,⟨d,hd,a,ha,htri⟩,S.conv a,S.mem_opposite ha,S.triangle_rotate htri⟩
  · intro a ha
    rw [C.distrib (C.opposite hD) hP hprod hne]
    refine ⟨hAD ha,?_⟩
    obtain ⟨d,hd⟩ := hD.1
    obtain ⟨p,htri⟩ := hPoint d a
    exact ⟨S.conv d,S.mem_opposite hd,p,⟨d,hd,a,ha,htri⟩,
      S.triangle_rotate_back (S.triangle_cycle htri)⟩

/-- The supported singleton restrictions in their original directed orientation. -/
theorem restricted_pair_bilateral (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {D : S.Menu i j} {A : S.Menu j k} (c : S.Atom i k)
    (hD : StrongExact.Exact S D) (hA : StrongExact.Exact S A)
    (hDc : (restrictLeft S D A c).Nonempty)
    (hAc : (restrictRight S D A c).Nonempty) :
    restrictLeft S D A c ⊆ S.product {c} (S.opposite (restrictRight S D A c)) ∧
    restrictRight S D A c ⊆ S.product (S.opposite (restrictLeft S D A c)) {c} := by
  obtain ⟨hl,hr⟩ := Selectors.restricted_bilateral S C hPoint hEdge c hD hA hDc hAc
  refine ⟨hl,?_⟩
  intro a ha
  have h := hr (S.mem_opposite ha)
  have h' := S.mem_opposite h
  rw [S.product_opposite] at h'
  have hs : S.opposite ({S.conv c} : S.Menu k i) = {c} := by
    ext d
    change S.conv d = S.conv c ↔ d = c
    exact ⟨fun h => by simpa only [S.conv_invol] using congrArg S.conv h,congrArg S.conv⟩
  simpa only [S.conv_invol,hs] using h'

end CCO.SafeReadings
