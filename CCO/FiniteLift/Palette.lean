import CCO.FiniteLift.Kernel

/-! The quotient safe palette uses the ENTIRE real cross matrix.
Logical equality is explicitly excluded. -/

universe v w t
namespace CCO.FiniteLift

def quotientSafe {A Q : Type*} (π : A → Q) (safe : A → A → Prop)
    (c d : Q) : Prop :=
  c ≠ d ∧ ∀ x y, π x = c → π y = d → safe x y

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (K : ExactKernel S G)

/-- All fine diversity names appearing anywhere in the complete matrix. -/
def matrixSupport (c d : K.Q) : Set (S.Atom () ()) :=
  {a | ∃ x y, K.proj x = c ∧ K.proj y = d ∧ S.colour x y = some a}

def quotientSafePalette (safe : Set (S.Atom () ())) (c d : K.Q) : Prop :=
  c ≠ d ∧ matrixSupport S K c d ⊆ safe

theorem quotientSafePalette_iff (safe : Set (S.Atom () ())) (c d : K.Q) :
    quotientSafePalette S K safe c d ↔ quotientSafe K.proj (S.menuRel safe) c d := by
  constructor
  · rintro ⟨hne, hsafe⟩
    refine ⟨hne, ?_⟩
    intro x y hx hy
    have hxy : x ≠ y := fun h => hne (hx.symm.trans ((congrArg K.proj h).trans hy))
    cases hc : S.colour x y with
    | none =>
      have heq := (S.colour_none_iff x y).mp hc
      exact False.elim (hxy (eq_of_heq (Sigma.mk.inj_iff.mp heq).2))
    | some a => exact ⟨a, hsafe ⟨x, y, hx, hy, hc⟩, hc⟩
  · rintro ⟨hne, hsafe⟩
    refine ⟨hne, ?_⟩
    rintro a ⟨x, y, hx, hy, hc⟩
    obtain ⟨b, hb, hcol⟩ := hsafe x y hx hy
    have hab : a = b := Option.some.inj (hc.symm.trans hcol)
    exact hab ▸ hb

/-- Moving the whole pair of classes moves the ENTIRE cross matrix. -/
theorem matrixSupport_smul (H : HomogeneousSource S G) (g : G) (c d : K.Q) :
    matrixSupport S K (g • c) (g • d) = matrixSupport S K c d := by
  ext a
  constructor
  · rintro ⟨x, y, hx, hy, hc⟩
    refine ⟨g⁻¹ • x, g⁻¹ • y, ?_, ?_, ?_⟩
    · rw [K.proj_smul, hx, inv_smul_smul]
    · rw [K.proj_smul, hy, inv_smul_smul]
    · exact (S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g⁻¹ x y).trans hc
  · rintro ⟨x, y, hx, hy, hc⟩
    refine ⟨g • x, g • y, ?_, ?_, ?_⟩
    · rw [K.proj_smul, hx]
    · rw [K.proj_smul, hy]
    · exact (S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g x y).trans hc

/-- The support depends only on the actual old-group quotient orbital,
including when its FULL automorphism group has more elements. -/
theorem matrixSupport_eq_of_orbital (H : HomogeneousSource S G)
    {c d c' d' : K.Q}
    (hp : GroupActions.orbital (G := G) c d c' d') :
    matrixSupport S K c' d' = matrixSupport S K c d := by
  obtain ⟨g, rfl, rfl⟩ := hp
  exact matrixSupport_smul S K H g c d

theorem quotientSafePalette_smul (H : HomogeneousSource S G)
    (safe : Set (S.Atom () ())) (g : G) (c d : K.Q) :
    quotientSafePalette S K safe (g • c) (g • d) ↔
      quotientSafePalette S K safe c d := by
  unfold quotientSafePalette
  rw [matrixSupport_smul S K H]
  exact and_congr (not_congr (MulAction.injective g).eq_iff) Iff.rfl

end CCO.FiniteLift
