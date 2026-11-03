import CCO.TypedRelation

/-!
# B051 source09 TNR: quotient-diagonal composition forces one involution

On an arbitrary ACTUAL quotient carrier, two symmetric serial relations
R and T satisfying R;T ⊆ logical diagonal must coincide and be the graph
of ONE involutive total function.

For a genuinely equivariant R, that same involution is equivariant for
the actual original group's induced action. This is the pure relational
heart of the pinned source09 no-return proof, not yet its full original
J-cut/index-two contradiction.

No quotient SAP, additional action section, FULL NR2, CCO, finite
cardinality or synthetic diversity identity is assumed.
-/

universe u v

namespace CCO.TerminalProfiles

/-- SOURCE09 C07–C09 pure quotient core.
Actual seriality and symmetricity together with the literal RAW
R;T ⊆ Delta force exactly one common involutive neighbour map. -/
theorem symmetric_serial_diagonal_comp_common_involution
    {Q : Type u}
    (R T : Q → Q → Prop)
    (hRsym : ∀ x y, R x y → R y x)
    (hTsym : ∀ x y, T x y → T y x)
    (hRserial : ∀ x, ∃ y, R x y)
    (hTserial : ∀ x, ∃ y, T x y)
    (hDiag : ∀ x y z, R x y → T y z → x = z) :
    ∃ f : Q → Q,
      (∀ x y, R x y ↔ f x = y) ∧
      (∀ x y, T x y ↔ f x = y) ∧
      (∀ x, f (f x) = x) := by
  classical
  have hRT : ∀ x y, R x y → T x y := by
    intro x y hxy
    obtain ⟨z, hyz⟩ := hTserial y
    have hxz : x = z := hDiag x y z hxy hyz
    subst z
    exact hTsym y x hyz
  have hTR : ∀ x y, T x y → R x y := by
    intro x y hxy
    obtain ⟨z, hyz⟩ := hRserial y
    have hzy : R z y := hRsym y z hyz
    have hyx : T y x := hTsym x y hxy
    have hzx : z = x := hDiag z y x hzy hyx
    subst z
    exact hRsym y x hyz
  have hUnique (x : Q) : ∃! y : Q, R x y := by
    obtain ⟨y, hxy⟩ := hRserial x
    refine ⟨y, hxy, ?_⟩
    intro z hxz
    have hyx : R y x := hRsym x y hxy
    have hTxz : T x z := hRT x z hxz
    exact (hDiag y x z hyx hTxz).symm
  let f : Q → Q := fun x => Classical.choose (hUnique x)
  have hF (x : Q) : R x (f x) :=
    (Classical.choose_spec (hUnique x)).1
  have hOnly (x y : Q) (hxy : R x y) : y = f x :=
    (Classical.choose_spec (hUnique x)).2 y hxy
  have hRiff (x y : Q) : R x y ↔ f x = y := by
    constructor
    · intro hxy
      exact (hOnly x y hxy).symm
    · intro hxy
      rw [← hxy]
      exact hF x
  have hTiff (x y : Q) : T x y ↔ f x = y := by
    constructor
    · intro hxy
      exact (hRiff x y).mp (hTR x y hxy)
    · intro hxy
      exact hRT x y ((hRiff x y).mpr hxy)
  have hInv (x : Q) : f (f x) = x := by
    have hBack : R (f x) x := hRsym x (f x) (hF x)
    exact (hRiff (f x) x).mp hBack
  exact ⟨f, hRiff, hTiff, hInv⟩

/-- SOURCE09 C10: if the quotient relation R is invariant under its
actual original-group action, the common involution is equivariant.
No group-action section or new quotient homogeneity is assumed. -/
theorem symmetric_serial_diagonal_comp_equivariant_involution
    {Q : Type u} {G : Type v} [Group G] [MulAction G Q]
    (R T : Q → Q → Prop)
    (hRsym : ∀ x y, R x y → R y x)
    (hTsym : ∀ x y, T x y → T y x)
    (hRserial : ∀ x, ∃ y, R x y)
    (hTserial : ∀ x, ∃ y, T x y)
    (hDiag : ∀ x y z, R x y → T y z → x = z)
    (hInvariant : ∀ g : G, ∀ x y, R x y → R (g • x) (g • y)) :
    ∃ f : Q → Q,
      (∀ x y, R x y ↔ f x = y) ∧
      (∀ x y, T x y ↔ f x = y) ∧
      (∀ x, f (f x) = x) ∧
      (∀ g : G, ∀ x, f (g • x) = g • f x) := by
  obtain ⟨f, hRiff, hTiff, hInv⟩ :=
    symmetric_serial_diagonal_comp_common_involution
      R T hRsym hTsym hRserial hTserial hDiag
  refine ⟨f, hRiff, hTiff, hInv, ?_⟩
  intro g x
  have hEdge : R x (f x) := (hRiff x (f x)).mpr rfl
  exact (hRiff (g • x) (g • f x)).mp (hInvariant g x (f x) hEdge)

end CCO.TerminalProfiles
