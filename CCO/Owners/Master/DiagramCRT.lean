import CCO.Owners.Master.DiagramStep

/-! Old compatible tuples and one common local coordinate reconstruct
every new compatible tuple uniquely.  Families may be empty, repeated or
incomparable; no map from an old index to the new owner is invented. -/

universe u v z
namespace CCO.Owners.Master.Diagram
variable {P : Type u} [DecidableEq P]
variable {A : Ambient.{u,v} P} {Valid : Finset P → Prop} {U : Finset P}

theorem erase_biUnion {I : Type z} [Fintype I] (f : I → Finset P) (p : P) :
    Finset.univ.biUnion (fun i => (f i).erase p) = (Finset.univ.biUnion f).erase p := by
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase]
  exact ⟨fun ⟨i,hne,hi⟩ => ⟨hne,i,hi⟩, fun ⟨hne,i,hi⟩ => ⟨i,hne,hi⟩⟩

namespace Step
variable {B : Stage A Valid U} {p : P} {O : Finset P} (S : Step B p O)
include S

/-- The erased original compatible tuple is compatible in the old diagram,
including mixed old/new pairs. -/
theorem erased_compatible {I : Type z} (f : I → Finset P) (b : ∀ i, A.X (f i))
    (compat : A.Compatible f b) :
    A.Compatible (fun i => (f i).erase p)
      (fun i => A.r (Finset.erase_subset p (f i)) (b i)) := by
  intro i j
  have hsub : (f i).erase p ∩ (f j).erase p ⊆ f i ∩ f j :=
    Finset.inter_subset_inter (Finset.erase_subset p (f i)) (Finset.erase_subset p (f j))
  have h := congrArg (A.r hsub) (compat i j)
  simpa only [Ambient.project_comp] using h

/-- Complete all-family CRT preservation. The finite maps and their
surjectivity have already been proved by `Step.stage`. -/
theorem stage_crt
    (validUnion : ∀ {I : Type z} [Fintype I] (f : I → Finset P),
      (∀ i, Valid (f i)) → Valid (Finset.univ.biUnion f))
    (oldCRT : B.CRT.{u,v,z}) : S.stage.CRT.{u,v,z} := by
  intro I _ f valid within b member compat
  let F := Finset.univ.biUnion f
  have fiF : ∀ i, f i ⊆ F := fun i => Finset.subset_biUnion_of_mem f (Finset.mem_univ i)
  have hF : Valid F := validUnion f valid
  have hFS : F ⊆ insert p U := Finset.biUnion_subset.mpr (fun i _ => within i)
  by_cases hpF : p ∈ F
  · let g : I → Finset P := fun i => (f i).erase p
    let c : ∀ i, A.X (g i) := fun i => A.r (Finset.erase_subset p (f i)) (b i)
    have validG : ∀ i, Valid (g i) := fun i => S.valid_erase (f i) (valid i) (within i)
    have withinG : ∀ i, g i ⊆ U := fun i => S.erase_subset_old (within i)
    have memberG : ∀ i, c i ∈ B.B (g i) := by
      intro i
      apply (S.mem_new_old (Finset.notMem_erase p (f i)) _).mp
      exact S.new_mapsTo (valid i) (validG i) (within i)
        (Finset.erase_subset p (f i)) (b i) (member i)
    have compatG : A.Compatible g c := S.erased_compatible f b compat
    have hUnion : Finset.univ.biUnion g = F.erase p := erase_biUnion f p
    have crtG : ∃! a : A.X (F.erase p), a ∈ B.B (F.erase p) ∧
        ∀ i, A.r ((Finset.erase_subset_erase p (fiF i))) a = c i := by
      have general (T : Finset P) (heq : Finset.univ.biUnion g = T)
          (hs : ∀ i, g i ⊆ T) :
          ∃! a : A.X T, a ∈ B.B T ∧ ∀ i, A.r (hs i) a = c i := by
        subst T
        exact oldCRT g validG withinG c memberG compatG
      exact general (F.erase p) hUnion (fun i => Finset.erase_subset_erase p (fiF i))
    obtain ⟨a,ha,hunique⟩ := crtG
    obtain ⟨i₀,_,hpi₀⟩ := Finset.mem_biUnion.mp hpF
    have hQ₀ := S.principal_subset (valid i₀) (within i₀) hpi₀
    let d : A.X (insert p O) := A.r hQ₀ (b i₀)
    have hd : d ∈ S.localSet :=
      ((S.mem_new_new hpi₀ hQ₀ (b i₀)).mp (member i₀)).2
    have common : ∀ i (hpi : p ∈ f i),
        A.r (S.principal_subset (valid i) (within i) hpi) (b i) = d := by
      intro i hpi
      have hQi := S.principal_subset (valid i) (within i) hpi
      have hsub : insert p O ⊆ f i ∩ f i₀ := Finset.subset_inter hQi hQ₀
      have h := congrArg (A.r hsub) (compat i i₀)
      simpa only [Ambient.project_comp] using h
    have owner : A.r (S.owner_erase F hF hFS hpF) a =
        A.r (Finset.subset_insert p O) d := by
      calc
        _ = A.r (S.owner_erase (f i₀) (valid i₀) (within i₀) hpi₀)
            (A.r (Finset.erase_subset_erase p (fiF i₀)) a) := by
          simp only [Ambient.project_comp]
        _ = A.r (S.owner_erase (f i₀) (valid i₀) (within i₀) hpi₀) (c i₀) :=
          congrArg (A.r (S.owner_erase (f i₀) (valid i₀) (within i₀) hpi₀)) (ha.2 i₀)
        _ = _ := by dsimp [c,d]; simp only [Ambient.project_comp]
    obtain ⟨x,hx,hxunique⟩ := S.glue F hF hFS hpF a d owner
    have xmember : x ∈ S.stage.B F :=
      (S.mem_new_new hpF (S.principal_subset hF hFS hpF) x).mpr
        ⟨hx.1 ▸ ha.1,hx.2 ▸ hd⟩
    have xcoordinates : ∀ i, A.r (fiF i) x = b i := by
      intro i
      by_cases hpi : p ∈ f i
      · apply S.pair_injective (f i) (valid i) (within i) hpi
        apply Prod.ext
        · change A.r (Finset.erase_subset p (f i)) (A.r (fiF i) x) = c i
          calc
            _ = A.r (Finset.erase_subset_erase p (fiF i))
                (A.r (Finset.erase_subset p F) x) := by
              simp only [Ambient.project_comp]
            _ = A.r (Finset.erase_subset_erase p (fiF i)) a :=
              congrArg (A.r (Finset.erase_subset_erase p (fiF i))) hx.1
            _ = _ := ha.2 i
        · change A.r (S.principal_subset (valid i) (within i) hpi) (A.r (fiF i) x) =
              A.r (S.principal_subset (valid i) (within i) hpi) (b i)
          calc
            _ = A.r (S.principal_subset hF hFS hpF) x := by
              simp only [Ambient.project_comp]
            _ = d := hx.2
            _ = _ := (common i hpi).symm
      · have hback : f i ⊆ (f i).erase p := by
          intro q hq
          exact Finset.mem_erase.mpr ⟨fun he => hpi (he ▸ hq),hq⟩
        have hinj : Function.Injective (A.r (Finset.erase_subset p (f i))) := by
          intro t t' he
          have hh := congrArg (A.r hback) he
          simpa only [Ambient.project_comp,Ambient.project_self] using hh
        apply hinj
        calc
          _ = A.r (Finset.erase_subset_erase p (fiF i))
              (A.r (Finset.erase_subset p F) x) := by
            simp only [Ambient.project_comp]
          _ = A.r (Finset.erase_subset_erase p (fiF i)) a :=
            congrArg (A.r (Finset.erase_subset_erase p (fiF i))) hx.1
          _ = _ := ha.2 i
    refine ⟨x,⟨xmember,xcoordinates⟩,?_⟩
    intro y hy
    have hyfirst := ((S.mem_new_new hpF (S.principal_subset hF hFS hpF) y).mp hy.1).1
    have hfirst : A.r (Finset.erase_subset p F) y = a := by
      apply hunique
      refine ⟨hyfirst,?_⟩
      intro i
      calc
        _ = A.r (Finset.erase_subset p (f i)) (A.r (fiF i) y) := by
          simp only [Ambient.project_comp]
        _ = A.r (Finset.erase_subset p (f i)) (b i) :=
          congrArg (A.r (Finset.erase_subset p (f i))) (hy.2 i)
    have hsecond : A.r (S.principal_subset hF hFS hpF) y = d := by
      calc
        _ = A.r hQ₀ (A.r (fiF i₀) y) := by simp only [Ambient.project_comp]
        _ = A.r hQ₀ (b i₀) := congrArg (A.r hQ₀) (hy.2 i₀)
        _ = d := rfl
    exact (hxunique y ⟨hfirst,hsecond⟩)
  · have withinOld : ∀ i, f i ⊆ U := by
      intro i
      exact S.old_subset (within i) (fun hp => hpF (fiF i hp))
    have memberOld : ∀ i, b i ∈ B.B (f i) := by
      intro i
      exact (S.mem_new_old (fun hp => hpF (fiF i hp)) (b i)).mp (member i)
    obtain ⟨x,hx,hunique⟩ := oldCRT f valid withinOld b memberOld compat
    refine ⟨x,⟨(S.mem_new_old hpF x).mpr hx.1,hx.2⟩,?_⟩
    intro y hy
    exact hunique y ⟨(S.mem_new_old hpF y).mp hy.1,hy.2⟩

end Step
end CCO.Owners.Master.Diagram
