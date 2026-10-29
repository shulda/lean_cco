import CCO.Owners.Master.CoordinateCoverage
import CCO.Owners.Master.StageData

/-! The final finite diagram is the complete quotient system of ONE
actual finite real subset. This follows from onto carrier maps, rather
than being an extra compatibility or representation premise. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} (D : SourceStage.{v,w,t,z} S H cco T Finset.univ)

def realCarrier : Set A := coordinateProjection S H cco Finset.univ ⁻¹' D.finite.B Finset.univ

theorem top_projection_injective :
    Function.Injective (coordinateProjection S H cco Finset.univ) := by
  intro x y hxy
  have hrel := Quotient.exact hxy
  change (coordinateKernel S H cco Finset.univ).val x y at hrel
  have hK : (coordinateKernel S H cco Finset.univ).val = (⊥ : Setoid A) :=
    congrArg Subtype.val (coordinateKernel_univ S H cco)
  rw [hK] at hrel
  exact hrel

theorem realCarrier_finite : (realCarrier S H cco D).Finite :=
  Set.Finite.of_injOn (f := coordinateProjection S H cco Finset.univ)
    (s := realCarrier S H cco D) (t := D.finite.B Finset.univ)
    (fun _ hx => hx) (top_projection_injective S H cco).injOn
    (D.finite.finite Finset.univ (by intro _ _ _ _; exact Finset.mem_univ _) (Finset.Subset.refl _))

theorem realCarrier_contains : T ⊆ realCarrier S H cco D := by
  intro a ha
  exact D.decorations.contains Finset.univ (by intro _ _ _ _; exact Finset.mem_univ _) (Finset.Subset.refl _)
    ⟨a,ha,rfl⟩

theorem realCarrier_nonempty : (realCarrier S H cco D).Nonempty := by
  obtain ⟨q,hq⟩ := D.finite.nonempty Finset.univ (by intro _ _ _ _; exact Finset.mem_univ _) (Finset.Subset.refl _)
  obtain ⟨a,rfl⟩ := (Quotient.mk''_surjective :
    Function.Surjective (coordinateProjection S H cco Finset.univ)) q
  exact ⟨a,hq⟩

/-- Every finite diagram object equals the actual projection image of
the one final real carrier, including the singleton empty coordinate. -/
theorem realCarrier_image (V : Finset (Position S H cco)) (hV : IsUpset V) :
    coordinateProjection S H cco V '' realCarrier S H cco D = D.finite.B V := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact D.finite.mapsTo (by intro _ _ _ _; exact Finset.mem_univ _) hV (Finset.Subset.refl _)
      (Finset.subset_univ V) (coordinateProjection S H cco Finset.univ a) ha
  · intro hy
    obtain ⟨q,hq,hqy⟩ := D.finite.onto (by intro _ _ _ _; exact Finset.mem_univ _) hV (Finset.Subset.refl _)
      (Finset.subset_univ V) y hy
    obtain ⟨a,rfl⟩ := (Quotient.mk''_surjective :
      Function.Surjective (coordinateProjection S H cco Finset.univ)) q
    exact ⟨a,hq,hqy⟩

end
end CCO.Owners.Master
