import CCO.FullRows.GaugeNatural
import CCO.FullRows.Rows
import CCO.SafeReadings.MovingReadings

/-! The full cross-packet matrix is forced by the SAME moving reading.
The second endpoint law follows from the actual diagonal pure action;
no independent choice of right readings is introduced. -/
universe u v w z t r
namespace CCO.FullRows
noncomputable section
open SafeReadings Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (Q : EndpointGauge S A K)
variable (h : HereditarySelector S)

theorem parameter_phases {I : Type*} (x y : Vertex I K) :
    parameter x y = parameter (x.1,1) (y.1,1)*x.2*y.2 := by
  simp only [parameter,chi,one_mul]
  ac_rfl

def readingName (g : K) (D : TaggedMenu S) (hD : IsExact S D) : N :=
  A.label (reading Q h g D.2.2 hD)

theorem readingName_congr (g : K) {D F : TaggedMenu S} (hD : IsExact S D) (hF : IsExact S F)
    (he : D = F) : readingName Q h g D hD = readingName Q h g F hF := by
  subst F
  rfl

theorem readingName_mem (g : K) (D : TaggedMenu S) (hD : IsExact S D) :
    readingName Q h g D hD ∈ names S A.label D :=
  ⟨reading Q h g D.2.2 hD,reading_member Q h g D.2.2 hD,rfl⟩

theorem readingName_covariant_of_names (hCov : h.Covariant S A) (γ : Γ) (g : K)
    (D F : TaggedMenu S) (hD : IsExact S D) (hF : IsExact S F)
    (hs : F.1 = A.tag γ D.1) (ht : F.2.1 = A.tag γ D.2.1)
    (hn : names S A.label F = names S A.label D) :
    readingName Q h g F hF = readingName Q h g D hD := by
  have he : A.act γ D = F := by
    apply A.tagged_names_injective
    · exact ⟨(A.source γ D).trans hs.symm,(A.target γ D).trans ht.symm⟩
    · exact (A.literal γ D).trans hn.symm
  exact (readingName_congr Q h g ((A.exact γ D).mpr hD) hF he).symm.trans
    (reading_covariant Q h hCov γ g D hD)

theorem readingName_singleton (g : K) (D : TaggedMenu S) (hD : IsExact S D)
    (n : N) (hn : names S A.label D = {n}) : readingName Q h g D hD = n :=
  Set.mem_singleton_iff.mp (hn ▸ readingName_mem Q h g D hD)

theorem reading_right_switch_label (hCov : h.Covariant S A) (u v : K)
    {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
    A.label (reading Q h (u*v) (Q.rightMenu v D) (Q.right_exact v hD)) =
      Q.switch v (A.label (reading Q h u D hD)) := by
  have hc := reading_covariant Q h hCov (Q.diagonal v) (u*v)
    ⟨Q.owner v i,j,Q.leftMenu v D⟩ (Q.left_exact v hD)
  have he := readingName_congr Q h (u*v)
    (D := A.act (Q.diagonal v) ⟨Q.owner v i,j,Q.leftMenu v D⟩)
    (F := ⟨i,Q.owner v j,Q.rightMenu v D⟩)
    ((A.exact _ _).mpr (Q.left_exact v hD)) (Q.right_exact v hD)
    (diagonal_left_eq_right Q v D)
  calc
    A.label (reading Q h (u*v) (Q.rightMenu v D) (Q.right_exact v hD)) =
        A.label (reading Q h (u*v) (Q.leftMenu v D) (Q.left_exact v hD)) := he.symm.trans hc
    _ = A.label (Q.left v (reading Q h u D hD)) := congrArg A.label (reading_switch Q h u v D hD)
    _ = _ := Q.left_label v _

theorem gaugeMenu_eq_left_right (g k : K) {i j : ι} (D : S.Menu i j) :
    gaugeMenu Q g k D = Q.leftMenu g (Q.rightMenu k D) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨Q.right k b,⟨b,hb,rfl⟩,rfl⟩
  · rintro ⟨b,⟨d,hd,rfl⟩,rfl⟩
    exact ⟨d,hd,rfl⟩

/-- ALL independent endpoint shifts give the literal matrix law, with
both owner types moved, and one fixed original reading parameter u. -/
theorem reading_matrix_label (hCov : h.Covariant S A) (u g k : K)
    {i j : ι} (D : S.Menu i j) (hD : StrongExact.Exact S D)
    (hT : StrongExact.Exact S (gaugeMenu Q g k D)) :
    A.label (reading Q h (u*g*k) (gaugeMenu Q g k D) hT) =
      Q.switch (g*k) (A.label (reading Q h u D hD)) := by
  have he := gaugeMenu_eq_left_right Q g k D
  have hh : StrongExact.Exact S (Q.leftMenu g (Q.rightMenu k D)) :=
    Q.left_exact g (Q.right_exact k hD)
  have hc := congrArg A.label (reading_switch Q h (u*k) g (Q.rightMenu k D) (Q.right_exact k hD))
  have hp : u*g*k = (u*k)*g := by ac_rfl
  have ht : (⟨Q.owner g i,Q.owner k j,gaugeMenu Q g k D⟩ : TaggedMenu S) =
      ⟨Q.owner g i,Q.owner k j,Q.leftMenu g (Q.rightMenu k D)⟩ :=
    congrArg (fun M : S.Menu (Q.owner g i) (Q.owner k j) => (⟨Q.owner g i,Q.owner k j,M⟩ : TaggedMenu S)) he
  have hn := readingName_congr Q h (u*g*k)
    (D := ⟨Q.owner g i,Q.owner k j,gaugeMenu Q g k D⟩)
    (F := ⟨Q.owner g i,Q.owner k j,Q.leftMenu g (Q.rightMenu k D)⟩) hT hh ht
  calc
    A.label (reading Q h (u*g*k) (gaugeMenu Q g k D) hT) =
        A.label (reading Q h ((u*k)*g) (Q.leftMenu g (Q.rightMenu k D)) hh) := by
      exact hn.trans (congrArg (fun q => A.label (reading Q h q (Q.leftMenu g (Q.rightMenu k D)) hh)) hp)
    _ = Q.switch g (A.label (reading Q h (u*k) (Q.rightMenu k D) (Q.right_exact k hD))) :=
      hc.trans (Q.left_label g _)
    _ = Q.switch g (Q.switch k (A.label (reading Q h u D hD))) :=
      congrArg (Q.switch g) (reading_right_switch_label Q h hCov u k D hD)
    _ = _ := by rw [map_mul]; rfl
end
end CCO.FullRows
