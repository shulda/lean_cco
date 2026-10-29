import CCO.Owners.Master.DiagramCRT

/-! Singleton initial systems, the empty-family boundary and the natural
compatible-coordinate bijection on every finite stage. -/

universe u v z
namespace CCO.Owners.Master.Diagram
variable {P : Type u} [DecidableEq P]
variable (A : Ambient.{u,v} P) (Valid : Finset P → Prop)

/-- Only the empty index is available initially; invalid indices require
no arbitrary inhabitant or equality cast. -/
def singletonSet (a : A.X ∅) (V : Finset P) : Set (A.X V) :=
  {x | ∃ h : V ⊆ ∅, A.r h a = x}

theorem singletonSet_subsingleton (a : A.X ∅) (V : Finset P) :
    (singletonSet A a V).Subsingleton := by
  rintro x ⟨h,rfl⟩ y ⟨k,rfl⟩
  rfl

def singletonStage (a : A.X ∅) : Stage A Valid ∅ where
  B := singletonSet A a
  finite V _ _ := (singletonSet_subsingleton A a V).finite
  nonempty V _ hV := ⟨A.r hV a,hV,rfl⟩
  mapsTo _ _ _ hWV x hx := by
    obtain ⟨hV,rfl⟩ := hx
    exact ⟨hWV.trans hV,(A.r_comp hV hWV a).symm⟩
  onto _ _ hV hWV y hy := by
    obtain ⟨hW,rfl⟩ := hy
    exact ⟨A.r hV a,⟨hV,rfl⟩,A.r_comp hV hWV a⟩

theorem singletonStage_crt (a : A.X ∅) : (singletonStage A Valid a).CRT.{u,v,z} := by
  intro I _ f _ within b member _
  let F := Finset.univ.biUnion f
  have hF : F ⊆ ∅ := Finset.biUnion_subset.mpr (fun i _ => within i)
  let x := A.r hF a
  have hx : x ∈ (singletonStage A Valid a).B F := ⟨hF,rfl⟩
  refine ⟨x,⟨hx,?_⟩,?_⟩
  · intro i
    obtain ⟨h,hb⟩ := member i
    exact (A.r_comp hF (Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) a).trans hb
  · intro y hy
    exact singletonSet_subsingleton A a F hy.1 hx

namespace Stage
variable {A Valid} {U : Finset P} (B : Stage A Valid U)

def CompatibleTuple {I : Type z} (f : I → Finset P) :=
  {b : ∀ i, B.Point (f i) // A.Compatible f (fun i => (b i).val)}

def coordinates {I : Type z} [Fintype I] (f : I → Finset P)
    (valid : ∀ i, Valid (f i)) (within : ∀ i, f i ⊆ U)
    (validUnion : Valid (Finset.univ.biUnion f)) :
    B.Point (Finset.univ.biUnion f) → B.CompatibleTuple f := fun x =>
  ⟨(fun i => ⟨A.r (Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) x.val,
    B.mapsTo validUnion (valid i) (Finset.biUnion_subset.mpr (fun j _ => within j))
      (Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) x.val x.property⟩),
    A.projected_compatible f _ (fun i => Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) x.val⟩

theorem coordinates_bijective (crt : B.CRT.{u,v,z}) {I : Type z} [Fintype I]
    (f : I → Finset P) (valid : ∀ i, Valid (f i)) (within : ∀ i, f i ⊆ U)
    (validUnion : Valid (Finset.univ.biUnion f)) :
    Function.Bijective (B.coordinates f valid within validUnion) := by
  constructor
  · intro x y he
    let q := B.coordinates f valid within validUnion x
    obtain ⟨w,hw,unique⟩ := crt f valid within (fun i => (q.val i).val)
      (fun i => (q.val i).property) q.property
    apply Subtype.ext
    apply (unique x.val ⟨x.property,fun _ => rfl⟩).trans
    symm
    apply unique y.val
    refine ⟨y.property,?_⟩
    intro i
    exact (congrArg (fun z : B.CompatibleTuple f => (z.val i).val) he).symm
  · intro q
    obtain ⟨x,hx,-⟩ := crt f valid within (fun i => (q.val i).val)
      (fun i => (q.val i).property) q.property
    refine ⟨⟨x,hx.1⟩,?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact hx.2 i

noncomputable def coordinateEquiv (crt : B.CRT.{u,v,z}) {I : Type z} [Fintype I]
    (f : I → Finset P) (valid : ∀ i, Valid (f i)) (within : ∀ i, f i ⊆ U)
    (validUnion : Valid (Finset.univ.biUnion f)) :
    B.Point (Finset.univ.biUnion f) ≃ B.CompatibleTuple f :=
  Equiv.ofBijective (B.coordinates f valid within validUnion)
    (B.coordinates_bijective crt f valid within validUnion)

end Stage
end CCO.Owners.Master.Diagram
