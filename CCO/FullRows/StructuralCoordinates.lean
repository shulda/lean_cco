import CCO.FullRows.Defs

/-! Structural coordinates come from REAL regular packets. No owner
equation is used to select their offsets. -/
universe u v w
namespace CCO.FullRows
variable {I : Type u} {K : Type v} [CommGroup K]

def Equivariant (e : Equiv.Perm (I × K)) : Prop :=
  ∀ g (p : I × K), e (p.1,g*p.2) = ((e p).1,g*(e p).2)

theorem coordinate_linear (e : Equiv.Perm (I × K)) (he : Equivariant e)
    (i : I) (z : K) : e (i,z) = ((e (i,1)).1,z*(e (i,1)).2) := by
  simpa only [mul_one] using he z (i,1)

theorem coordinateIndex_bijective (e : Equiv.Perm (I × K)) (he : Equivariant e) :
    Function.Bijective (fun i => (e (i,1)).1) := by
  constructor
  · intro i j hij
    have hh : e (i,1) = e (j,(e (i,1)).2 * ((e (j,1)).2)⁻¹) := by
      calc
        _ = ((e (j,1)).1,((e (i,1)).2 * ((e (j,1)).2)⁻¹) * (e (j,1)).2) := by
          apply Prod.ext
          · exact hij
          · simp
        _ = _ := (coordinate_linear e he j _).symm
    exact congrArg Prod.fst (e.injective hh)
  · intro j
    obtain ⟨⟨i,z⟩,hh⟩ := e.surjective (j,1)
    refine ⟨i,?_⟩
    exact congrArg Prod.fst ((coordinate_linear e he i z).symm.trans hh)

noncomputable def structuralOfEquivariant (e : Equiv.Perm (I × K))
    (he : Equivariant e) : Structural I K where
  sigma := Equiv.ofBijective (fun i => (e (i,1)).1) (coordinateIndex_bijective e he)
  offset := fun i => (e (i,1)).2

theorem structuralOfEquivariant_apply (e : Equiv.Perm (I × K))
    (he : Equivariant e) (p : I × K) :
    e p = baseMap (structuralOfEquivariant e he) p := by
  exact coordinate_linear e he p.1 p.2

theorem existsUnique_coordinates (e : Equiv.Perm (I × K)) (he : Equivariant e) :
    ∃! s : Structural I K, ∀ p, e p = baseMap s p := by
  refine ⟨structuralOfEquivariant e he,structuralOfEquivariant_apply e he,?_⟩
  intro s hs
  apply Structural.ext
  · apply Equiv.ext
    intro i
    have hh := congrArg Prod.fst (hs (i,1))
    exact hh.symm
  · funext i
    change s.offset i = (e (i,1)).2
    have hh := congrArg Prod.snd (hs (i,1))
    simpa only [baseMap,one_mul] using hh.symm

/-- Even with known owners, REAL image phases are the uniquely determined offsets. -/
theorem offset_from_real_image (e : Equiv.Perm (I × K)) (s : Structural I K)
    (hs : ∀ p, e p = baseMap s p) (i : I) : s.offset i = (e (i,1)).2 := by
  simpa only [baseMap,one_mul] using (congrArg Prod.snd (hs (i,1))).symm

/-- An owner stabilizer can make the owner equation alone nonunique. -/
theorem owner_stabilizer_ambiguity {B : Type w} [MulAction K B]
    (a : B) (g : K) (hg : g ≠ 1) (hga : g • a = a) :
    (1 : K) ≠ g ∧ (1 : K) • a = g • a := by
  exact ⟨Ne.symm hg,by simpa only [one_smul] using hga.symm⟩

end CCO.FullRows
