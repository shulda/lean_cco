import CCO.Atomic

/-!
# The precise two-step RAW / STRONG boundary

Equality-inclusive RAW composition can have diagonal outputs even if its
factors have only diversity atoms. STRONG products have only diversity
outputs. At length two the diversity restriction is exactly the actual
three-distinct-point triangle product, with NO SAP or CCO hypothesis.
Longer positive words require the separate SAP injectivization argument.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j k : ι}

/-- Diversity restriction of a represented RAW relation, tagged by
its literal ordered endpoint sort pair. -/
def diversityGuard (R : TRel X i j) : S.Menu i j :=
  { c | ∃ x y, R x y ∧ S.colour x y = some c }

/-- The colour-semantic embedding is inverse to diversity guard on
arbitrary menus because all diversity colours have actual witnesses. -/
theorem diversityGuard_menuRel (A : S.Menu i j) :
    S.diversityGuard (S.menuRel A) = A := by
  ext c
  constructor
  · rintro ⟨x, y, ⟨a, ha, hxy⟩, hc⟩
    have hca : c = a := by
      have h := hc.symm.trans hxy
      exact Option.some.inj h
    simpa only [hca] using ha
  · intro hc
    obtain ⟨x, y, hxy⟩ := S.realized c
    exact ⟨x, y, ⟨c, hc, hxy⟩, hxy⟩

/-- At exactly two letters, a diversity-endpoint RAW walk has three
pairwise distinct real vertices, including in repeated named sorts. -/
theorem product_eq_raw_two_step_guard
    (A : S.Menu i j) (B : S.Menu j k) :
    S.product A B =
      S.diversityGuard (TRel.comp (S.menuRel A) (S.menuRel B)) := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, ⟨x, y, z, hxy, hyz, hxz⟩⟩
    exact ⟨x, z, ⟨y, ⟨a, ha, hxy⟩, ⟨b, hb, hyz⟩⟩, hxz⟩
  · rintro ⟨x, z, ⟨y, ⟨a, ha, hxy⟩, ⟨b, hb, hyz⟩⟩, hxz⟩
    exact ⟨a, ha, b, hb, ⟨x, y, z, hxy, hyz, hxz⟩⟩

/-- A true RAW logical-identity relation has EMPTY STRONG diversity
restriction; it never becomes a strong identity letter or menu. -/
theorem diversityGuard_ident (i : ι) :
    S.diversityGuard (TRel.ident X i) =
      (∅ : S.Menu i i) := by
  ext a
  constructor
  · rintro ⟨x, y, hxy, hc⟩
    subst y
    have hn : S.colour x x = none :=
      (S.colour_none_iff x x).2 rfl
    rw [hn] at hc
    cases hc
  · intro ha
    exact False.elim (by simpa using ha)

/-- The one-atom RAW predicate is diversity-only, not literal equality. -/
theorem atomRel_as_menu (a : S.Atom i j) :
    S.atomRel a = S.menuRel ({a} : S.Menu i j) := by
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨a, by simp, h⟩
  · rintro ⟨b, hb, hc⟩
    have h : b = a := Set.mem_singleton_iff.mp hb
    change S.colour x y = some a
    simpa only [h] using hc

end CCO.AtomicSource
