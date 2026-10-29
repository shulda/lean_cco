import CCO.SafeReadings.GateSupport

universe u v w
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι} {Q : Family S}

private theorem opposite_singleton (a : S.Atom i j) :
    S.opposite ({a} : S.Menu i j) = {S.conv a} := by
  ext b
  change S.conv b = a ↔ b = S.conv a
  constructor
  · intro h
    have h' := congrArg S.conv h
    simpa only [S.conv_invol] using h'
  · rintro rfl
    exact S.conv_invol a

/-- The two original exact restrictions meet their own gates. -/
theorem restricted_meets_gate (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {A : S.Menu i j} {B : S.Menu j k} {D : S.Menu i k}
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ J)
    (hB : (⟨j,k,B⟩ : TaggedMenu S) ∈ J)
    (hD : (⟨i,k,D⟩ : TaggedMenu S) ∈ J) (hPC : S.PC A B D)
    {c : S.Atom i k} (hc : c ∈ gate S F D) :
    (restrictLeft S A B c ∩ gate S F A).Nonempty ∧
      (restrictRight S A B c ∩ gate S F B).Nonempty := by
  have hleft := gate_bilateral_left S C hF hJ hV hD hB (hJ.member hA) hPC.1 hPC.2.2 hc
  have hright := gate_bilateral_right S C hF hJ hV hD hA (hJ.member hB) hPC.1 hPC.2.1 hc
  obtain ⟨a,ha,b,hb,htri⟩ := hright
  obtain ⟨a',ha',b',hb',htri'⟩ := hleft
  constructor
  · exact ⟨a,⟨ha.1,c,by simp,S.conv b,S.mem_opposite hb,
      S.triangle_rotate htri⟩,ha⟩
  · exact ⟨b',⟨hb'.1,S.conv a',S.mem_opposite ha',c,by simp,
      S.triangle_rotate_back (S.triangle_cycle htri')⟩,hb'⟩

/-- C16 includes BOTH bilateral support inclusions for the restricted pair. -/
theorem restricted_bilateral (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {A : S.Menu i j} {B : S.Menu j k} (c : S.Atom i k)
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ Q) (hB : (⟨j,k,B⟩ : TaggedMenu S) ∈ Q)
    (hAc : (restrictLeft S A B c).Nonempty)
    (hBc : (restrictRight S A B c).Nonempty) :
    restrictLeft S A B c ⊆ S.product {c} (S.opposite (restrictRight S A B c)) ∧
    S.opposite (restrictRight S A B c) ⊆ S.product {S.conv c} (restrictLeft S A B c) := by
  have hcs := C.singleton c
  have hcbs := C.singleton (S.conv c)
  have hoppB := C.opposite hB
  have hprodA := C.product hcbs hA
  have hprodB := C.product hcs hoppB
  have hnOpp : (S.opposite (restrictRight S A B c)).Nonempty := by
    obtain ⟨b,hb⟩ := hBc
    exact ⟨S.conv b,S.mem_opposite hb⟩
  constructor
  · rw [opposite_restrictRight S]
    rw [C.distrib hcs hoppB hprodA (by simpa only [← opposite_restrictRight S] using hnOpp)]
    intro a ha
    refine ⟨ha.2,?_⟩
    have hdup := S.supported_fork_of_gluing hPoint hEdge c A ha.1
    rw [S.product_assoc_of_edge_gluing hEdge] at hdup
    exact hdup
  · rw [opposite_restrictRight S]
    rw [show restrictLeft S A B c = A ∩ S.product {c} (S.opposite B) from rfl]
    rw [C.distrib hcbs hA hprodB hAc]
    intro b hb
    refine ⟨hb.2,?_⟩
    have hdup := S.supported_fork_of_gluing hPoint hEdge (S.conv c) (S.opposite B) hb.1
    rw [S.conv_invol, S.product_assoc_of_edge_gluing hEdge] at hdup
    exact hdup

/-- Every atom in the third gate has a supported pair in the first two gates. -/
theorem gate_pc_first (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {F J : Family S} (hF : Filter S Q F) (hJ : Current S Q J)
    (hV : Visible S F J)
    {A : S.Menu i j} {B : S.Menu j k} {D : S.Menu i k}
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ J)
    (hB : (⟨j,k,B⟩ : TaggedMenu S) ∈ J)
    (hD : (⟨i,k,D⟩ : TaggedMenu S) ∈ J) (hPC : S.PC A B D) :
    gate S F D ⊆ S.product (gate S F A) (gate S F B) := by
  intro c hc
  obtain ⟨hAG,hBG⟩ := restricted_meets_gate S C hF hJ hV hA hB hD hPC hc
  have hAc : (⟨i,j,restrictLeft S A B c⟩ : TaggedMenu S) ∈ Q :=
    C.inter (hJ.member hA)
      (C.product (C.singleton c) (C.opposite (hJ.member hB)))
      (by obtain ⟨a,ha,_⟩ := hAG; exact ⟨a,ha⟩)
  have hBc : (⟨j,k,restrictRight S A B c⟩ : TaggedMenu S) ∈ Q :=
    C.inter (hJ.member hB)
      (C.product (C.opposite (hJ.member hA)) (C.singleton c))
      (by obtain ⟨b,hb,_⟩ := hBG; exact ⟨b,hb⟩)
  have hAj := hJ.downward hA hAc (fun _ h => h.1)
  have hBj := hJ.downward hB hBc (fun _ h => h.1)
  obtain ⟨hleft,hright⟩ := restricted_bilateral S C hPoint hEdge c
    (hJ.member hA) (hJ.member hB) (C.nonempty hAc) (C.nonempty hBc)
  have hSupports := gate_bilateral_left S C hF hJ hV hAj (hJ.opposite hBj)
    (C.singleton c) hleft (by simpa [opposite_singleton] using hright)
  obtain ⟨a,ha⟩ := gate_nonempty S C hF hJ hV hAj
  obtain ⟨d,hd,b,hb,htri⟩ := hSupports ha
  have hdc : d = c := Set.mem_singleton_iff.mp hd
  subst d
  rw [gate_opposite S hF] at hb
  refine ⟨a,?_,S.conv b,?_,S.triangle_rotate htri⟩
  · rw [gate_heredity S F (fun _ h => h.1) hAG] at ha
    exact ha.2
  · have hgb : S.conv b ∈ gate S F (restrictRight S A B c) := hb
    rw [gate_heredity S F (fun _ h => h.1) hBG] at hgb
    exact hgb.2

/-- C17: all THREE PC coordinates survive, including coinciding sorts or menus. -/
theorem gate_preserves_PC (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {F J : Family S} (hF : Filter S Q F) (hJ : Current S Q J)
    (hV : Visible S F J)
    {A : S.Menu i j} {B : S.Menu j k} {D : S.Menu i k}
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ J)
    (hB : (⟨j,k,B⟩ : TaggedMenu S) ∈ J)
    (hD : (⟨i,k,D⟩ : TaggedMenu S) ∈ J) (hPC : S.PC A B D) :
    S.PC (gate S F A) (gate S F B) (gate S F D) := by
  refine ⟨gate_pc_first S C hPoint hEdge hF hJ hV hA hB hD hPC,?_,?_⟩
  · have h := gate_pc_first S C hPoint hEdge hF hJ hV hD (hJ.opposite hB) hA
      ((S.pc_rotate_output_first A B D).mp hPC)
    simpa only [gate_opposite S hF] using h
  · have h := gate_pc_first S C hPoint hEdge hF hJ hV (hJ.opposite hA) hD hB
      ((S.pc_rotate_output_second A B D).mp hPC)
    simpa only [gate_opposite S hF] using h

end CCO.SafeReadings
