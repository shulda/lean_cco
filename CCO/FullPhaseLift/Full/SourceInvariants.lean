import CCO.FullPhaseLift.Full.SourceSAP

/-! Actual colour-invariant equivalences and their relative class sets
transport through the same complete typed source isomorphism. This is an
order isomorphism on ALL invariant equivalences, not an exact sublattice. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w u' v' w'
namespace CCO.FullPhaseLift.Full
open ParityHasse.Original
noncomputable section
variable {κ : Type u} {Y : κ → Type v} {ι : Type u'} {X : ι → Type v'}
variable {T : AtomicSource.{u,v,w} κ Y} {S : AtomicSource.{u',v',w'} ι X}
namespace SourceIso
variable (e : SourceIso T S) (k : κ)

/-- Direct pullback/pushforward of the SAME actual underlying equivalence
relations; colour names are only renamed by the already constructed iso. -/
def colourOrderIso : ColourEq T k ≃o ColourEq S (e.sort k) where
  toFun E := ⟨Setoid.comap (e.point k).symm E.val,by
    intro x y x' y' hc
    apply E.property
    apply Option.map_injective (e.atom k k).injective
    rw [e.colours,e.colours]
    simpa only [Equiv.apply_symm_apply] using hc⟩
  invFun E := ⟨Setoid.comap (e.point k) E.val,by
    intro x y x' y' hc
    apply E.property
    rw [← e.colours,← e.colours,hc]⟩
  left_inv E := by
    apply ColourEq.ext
    intro x y
    change E.val ((e.point k).symm (e.point k x)) ((e.point k).symm (e.point k y)) ↔ E.val x y
    simp only [Equiv.symm_apply_apply]
  right_inv E := by
    apply ColourEq.ext
    intro x y
    change E.val (e.point k ((e.point k).symm x)) (e.point k ((e.point k).symm y)) ↔ E.val x y
    simp only [Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro E F
    change (∀ ⦃x y : X (e.sort k)⦄,
      E.val ((e.point k).symm x) ((e.point k).symm y) →
      F.val ((e.point k).symm x) ((e.point k).symm y)) ↔
      (∀ ⦃x y : Y k⦄, E.val x y → F.val x y)
    constructor
    · intro h x y hxy
      have hh := @h (e.point k x) (e.point k y)
      have hh' : E x y → F x y := by
        simpa only [Setoid.comap,Function.onFun,Equiv.symm_apply_apply] using hh
      exact hh' hxy
    · intro h x y hxy
      exact @h _ _ hxy

@[simp] theorem colourOrderIso_rel (E : ColourEq T k) (x y : Y k) :
    (e.colourOrderIso k E) (e.point k x) (e.point k y) ↔ E x y := by
  change E.val ((e.point k).symm (e.point k x)) ((e.point k).symm (e.point k y)) ↔ E.val x y
  simp only [Equiv.symm_apply_apply]

def relativeFibreEquiv (F : ColourEq T k) (a : Y k) :
    {x // F a x} ≃ {x // (e.colourOrderIso k F) (e.point k a) x} where
  toFun x := ⟨e.point k x.val,(e.colourOrderIso_rel k F a x.val).mpr x.property⟩
  invFun x := ⟨(e.point k).symm x.val,by
    have h := x.property
    change F.val ((e.point k).symm (e.point k a)) ((e.point k).symm x.val) at h
    simpa only [Equiv.symm_apply_apply] using h⟩
  left_inv x := Subtype.ext ((e.point k).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((e.point k).apply_symm_apply x.val)

/-- Relative classes are carried by a genuine quotient equivalence,
so both infinitude and finite relative indices are preserved. -/
def relativeClassEquiv (E F : ColourEq T k) (a : Y k) :
    RelativeClass E.val F.val a ≃
      RelativeClass (e.colourOrderIso k E).val (e.colourOrderIso k F).val (e.point k a) :=
  Quotient.congr (e.relativeFibreEquiv k F a) (by
    intro x y
    exact (e.colourOrderIso_rel k E x.val y.val).symm)

theorem relativeIndex_eq (E F : ColourEq T k) (a : Y k) :
    relativeIndex E.val F.val a =
      relativeIndex (e.colourOrderIso k E).val (e.colourOrderIso k F).val (e.point k a) :=
  Nat.card_congr (e.relativeClassEquiv k E F a)

theorem finite_relativeClass_iff (E F : ColourEq T k) (a : Y k) :
    Finite (RelativeClass E.val F.val a) ↔
      Finite (RelativeClass (e.colourOrderIso k E).val
        (e.colourOrderIso k F).val (e.point k a)) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (e.relativeClassEquiv k E F a)
  · intro h
    letI := h
    exact Finite.of_equiv _ (e.relativeClassEquiv k E F a).symm

/-- Terminality concerns ALL proper relative intervals, and survives the
canonical sort/palette renaming with its actual class sets unchanged. -/
theorem terminal_interval_infinite
    (terminal : ∀ (E F : ColourEq S (e.sort k)), E < F → ∀ a,
      Infinite (RelativeClass E.val F.val a))
    (E F : ColourEq T k) (hEF : E < F) (a : Y k) :
    Infinite (RelativeClass E.val F.val a) := by
  letI := terminal (e.colourOrderIso k E) (e.colourOrderIso k F)
    ((e.colourOrderIso k).strictMono hEF) (e.point k a)
  exact Infinite.of_injective (e.relativeClassEquiv k E F a).symm
    (e.relativeClassEquiv k E F a).symm.injective

/-- A terminal child excludes every finite-relative cover after canonical
re-naming; actual relative class sets, cover order and indices survive. -/
theorem terminal_cover_infinite
    (terminal : ∀ (E F : ColourEq S (e.sort k)), E ⋖ F → ∀ a,
      Infinite (RelativeClass E.val F.val a))
    (E F : ColourEq T k) (hEF : E ⋖ F) (a : Y k) :
    Infinite (RelativeClass E.val F.val a) := by
  let f := e.colourOrderIso k
  have hmap : f E ⋖ f F := by
    refine ⟨f.strictMono hEF.lt,?_⟩
    intro C hEC hCF
    exact hEF.2 (by simpa only [f.symm_apply_apply] using f.symm.strictMono hEC)
      (by simpa only [f.symm_apply_apply] using f.symm.strictMono hCF)
  letI := terminal (f E) (f F) hmap (e.point k a)
  exact Infinite.of_injective (e.relativeClassEquiv k E F a).symm
    (e.relativeClassEquiv k E F a).symm.injective

end SourceIso
end
end CCO.FullPhaseLift.Full
