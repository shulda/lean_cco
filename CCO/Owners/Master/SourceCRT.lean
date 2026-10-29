import CCO.Owners.Master.SourceCarrier

/-! Finite image CRT in actual exact quotients.  The finite image of the
actual family meet is bijective with ALL pair-compatible finite image
tuples.  The empty meet is the actual ambient top equivalence. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

namespace FiniteImages
variable {A : Type v} {I : Type z}

def CompatibleTuple (B : Set A) (E : I → Setoid A) :=
  {q : ∀ i, Quotient (E i) // Abstract.Compatible E q ∧
    ∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i)) '' B}

def coordinates (B : Set A) (E : I → Setoid A) :
    ((Quotient.mk'' : A → Quotient (Abstract.familyMeet E)) '' B) →
      CompatibleTuple B E := fun x =>
  ⟨Abstract.coordinates E x.val, Abstract.coordinates_compatible E x.val,by
    obtain ⟨a,ha,he⟩ := x.property
    rw [← he]
    intro i
    exact ⟨a,ha,rfl⟩⟩

theorem coordinates_bijective (B : Set A) (E : I → Setoid A)
    (realize : ∀ q : ∀ i, Quotient (E i),
      (∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i)) '' B) →
      Abstract.Compatible E q → ∃ a ∈ B, ∀ i, Quotient.mk'' a = q i) :
    Function.Bijective (coordinates B E) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact Abstract.coordinates_injective E (congrArg Subtype.val he)
  · intro q
    obtain ⟨a,ha,hq⟩ := realize q.val q.property.2 q.property.1
    refine ⟨⟨Quotient.mk'' a,⟨a,ha,rfl⟩⟩,?_⟩
    apply Subtype.ext
    funext i
    exact hq i

noncomputable def coordinateEquiv (B : Set A) (E : I → Setoid A)
    (realize : ∀ q : ∀ i, Quotient (E i),
      (∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i)) '' B) →
      Abstract.Compatible E q → ∃ a ∈ B, ∀ i, Quotient.mk'' a = q i) :
    ((Quotient.mk'' : A → Quotient (Abstract.familyMeet E)) '' B) ≃
      CompatibleTuple B E :=
  Equiv.ofBijective (coordinates B E) (coordinates_bijective B E realize)
end FiniteImages

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} (D : SourceStage.{v,w,t,z} S H cco T Finset.univ)

/-- Every compatible tuple from the finite actual quotient images is
realized by a point of the ONE finite real carrier, not just an ambient
point or a tuple of separately chosen witnesses. -/
theorem realCarrier_realizes {I : Type z} [Fintype I] (E : I → Exact S H cco)
    (q : ∀ i, Quotient (E i).val)
    (member : ∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i).val) '' realCarrier S H cco D)
    (compat : Abstract.Compatible (fun i => (E i).val) q) :
    ∃ a ∈ realCarrier S H cco D, ∀ i, Quotient.mk'' a = q i := by
  classical
  obtain ⟨a,ha⟩ := exactCRT_real_representative S H cco () E q compat
  let f : I → Finset (Position S H cco) := fun i => exactPositions S H cco (E i)
  have valid : ∀ i, IsUpset (f i) := fun i => exactPositions_upset S H cco (E i)
  have member' : ∀ i, coordinateProjection S H cco (f i) a ∈ D.finite.B (f i) := by
    intro i
    rw [← realCarrier_image S H cco D (f i) (valid i)]
    obtain ⟨b,hb,hbq⟩ := member i
    refine ⟨b,hb,?_⟩
    apply Quotient.sound
    have hrel := Quotient.exact (hbq.trans (ha i).symm)
    change (E i).val b a at hrel
    change (coordinateKernel S H cco (f i)).val b a
    have hK : (coordinateKernel S H cco (f i)).val = (E i).val :=
      congrArg Subtype.val (coordinateKernel_exactPositions S H cco (E i))
    rw [hK]
    exact hrel
  have compat' : (exactAmbient S H cco).Compatible f
      (fun i => coordinateProjection S H cco (f i) a) := by
    intro i j
    rfl
  obtain ⟨x,hx,-⟩ := D.compatible f valid (fun _ => Finset.subset_univ _)
    (fun i => coordinateProjection S H cco (f i) a) member' compat'
  let F := Finset.univ.biUnion f
  have hF : IsUpset F := by
    intro p q hp hpq
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨i,hi,valid i hpi hpq⟩
  obtain ⟨y,hy,hyx⟩ := D.finite.onto (by intro _ _ _ _; exact Finset.mem_univ _) hF (Finset.Subset.refl _)
    (Finset.subset_univ F) x hx.1
  obtain ⟨b,rfl⟩ := (Quotient.mk''_surjective :
    Function.Surjective (coordinateProjection S H cco Finset.univ)) y
  refine ⟨b,hy,?_⟩
  intro i
  have coord : coordinateProjection S H cco (f i) b =
      coordinateProjection S H cco (f i) a := by
    calc
      _ = coordinateMap S H cco (Finset.subset_biUnion_of_mem f (Finset.mem_univ i))
          (coordinateMap S H cco (Finset.subset_univ F)
            (coordinateProjection S H cco Finset.univ b)) := rfl
      _ = coordinateMap S H cco (Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) x :=
        congrArg (coordinateMap S H cco
          (Finset.subset_biUnion_of_mem f (Finset.mem_univ i))) hyx
      _ = _ := hx.2 i
  have hrel := Quotient.exact coord
  have hE : (E i).val b a := by
    change (coordinateKernel S H cco (f i)).val b a at hrel
    have hK : (coordinateKernel S H cco (f i)).val = (E i).val :=
      congrArg Subtype.val (coordinateKernel_exactPositions S H cco (E i))
    rw [hK] at hrel
    exact hrel
  exact (Quotient.sound hE).trans (ha i)

theorem realCarrier_family_bijective {I : Type z} [Fintype I]
    (E : I → Exact S H cco) :
    Function.Bijective (FiniteImages.coordinates (realCarrier S H cco D) (fun i => (E i).val)) :=
  FiniteImages.coordinates_bijective _ _ (realCarrier_realizes S H cco D E)

end
end CCO.Owners.Master
