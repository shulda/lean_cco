import CCO.RealClosure.Bounds.Directions
import CCO.RealClosure.Bounds.Palette

/-! The elementary one-atom-per-direction injection is separate from CRT
and the exponential palette theorem. It needs no CCO or exactness premise. -/
noncomputable section
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

theorem exists_basic_direction_colour (D : Direction S) :
    ∃ a : OutsideAtom S H, a.val ∈ diversitySupport S D.val := by
  classical
  have hex : ∃ x y : M, D.val x y ∧ ¬ finitePacket S H x y := by
    by_contra hn
    apply D.property.1
    apply finiteClasses_of_le S (F := finitePacket S H) _ (finitePacket_finite S H)
    intro x y hxy
    by_contra hnot
    exact hn ⟨x,y,hxy,hnot⟩
  obtain ⟨x,y,hD,hF⟩ := hex
  have hne : x ≠ y := by rintro rfl; exact hF ((finitePacket S H).val.refl _)
  obtain ⟨a,ha⟩ := col_some_of_ne S hne
  exact ⟨⟨a,fun h => hF ((mem_diversitySupport S _ ha).mp h)⟩,x,y,hD,ha⟩

noncomputable def basicDirectionColour (D : Direction S) : OutsideAtom S H :=
  (exists_basic_direction_colour S H D).choose

theorem basicDirectionColour_injective : Function.Injective (basicDirectionColour S H) := by
  intro D E he
  by_contra hne
  have hval : D.val ≠ E.val := fun h => hne (Subtype.ext h)
  have hle := le_finitePacket S H (D.val ⊓ E.val)
    (distinct_direction_inf_finite S D.property E.property hval)
  have hD := (exists_basic_direction_colour S H D).choose_spec
  have hE : (basicDirectionColour S H D).val ∈ diversitySupport S E.val := by
    rw [show (basicDirectionColour S H D).val = (basicDirectionColour S H E).val from
      congrArg Subtype.val he]
    exact (exists_basic_direction_colour S H E).choose_spec
  obtain ⟨x,y,hxy,hcol⟩ := hD
  have hpF : (basicDirectionColour S H D).val ∈ diversitySupport S (finitePacket S H) :=
    ⟨x,y,hle ⟨hxy,(mem_diversitySupport S E.val hcol).mp hE⟩,hcol⟩
  exact (basicDirectionColour S H D).property hpF

/-- C11's elementary weaker count, with a direct actual old-atom injection. -/
theorem directionCount_le_outside : directionCount S ≤ outsideAtomCount S H := by
  classical
  letI := S.finiteAtom () ()
  exact Nat.card_le_card_of_injective (basicDirectionColour S H)
    (basicDirectionColour_injective S H)
end CCO.RealClosure.Bounds
