import CCO.RigidGroupoid.Phase.AbstractCharacter
import Mathlib.CategoryTheory.Types.Basic

/-! A free groupoid action admits global character-compatible bit functions.
The proof chooses one seed per actual point orbit, including when infinitely
many point orbits occur. Prescribed bits impose exactly pairwise equations. -/

universe u v w
namespace CCO.RigidGroupoid.Phase.Abstract
open CategoryTheory
noncomputable section
variable {J : Type u} [Groupoid.{v} J] (F : J ⥤ Type w)

abbrev Point := Σ j, F.obj j

def Free : Prop := ∀ {a b : J} (R T : a ⟶ b) (q : F.obj a),
  F.map R q = F.map T q → R = T

def Orbit (p q : Point F) : Prop := ∃ R : p.1 ⟶ q.1, F.map R p.2 = q.2

theorem orbit_refl (p : Point F) : Orbit F p p := ⟨𝟙 _, F.map_id_apply _ _⟩

theorem orbit_symm {p q : Point F} (h : Orbit F p q) : Orbit F q p := by
  obtain ⟨R, hR⟩ := h
  refine ⟨inv R, ?_⟩
  rw [← hR, ← F.map_comp_apply]
  simp

theorem orbit_trans {p q r : Point F} (h : Orbit F p q) (k : Orbit F q r) :
    Orbit F p r := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨T, hT⟩ := k
  refine ⟨R ≫ T, ?_⟩
  rw [F.map_comp_apply, hR, hT]

def orbitSetoid : Setoid (Point F) where
  r := Orbit F
  iseqv := ⟨orbit_refl F, orbit_symm F, orbit_trans F⟩

abbrev OrbitClass := Quotient (orbitSetoid F)

def pointClass (p : Point F) : OrbitClass F := Quotient.mk _ p

theorem class_eq_iff {p q : Point F} : pointClass F p = pointClass F q ↔ Orbit F p q :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := orbitSetoid F) h⟩

/-- The transporting arrow is uniquely determined by its actual endpoints. -/
def transport {p q : Point F} (h : Orbit F p q) : p.1 ⟶ q.1 := Classical.choose h

theorem transport_spec {p q : Point F} (h : Orbit F p q) :
    F.map (transport F h) p.2 = q.2 := Classical.choose_spec h

theorem transport_unique (free : Free F) {p q : Point F} (h : Orbit F p q)
    (R : p.1 ⟶ q.1) (hR : F.map R p.2 = q.2) : transport F h = R :=
  free _ _ _ ((transport_spec F h).trans hR.symm)

def difference (χ : Character J) {p q : Point F} (h : Orbit F p q) : Bit :=
  χ.value (transport F h)

theorem difference_refl (free : Free F) (χ : Character J) (p : Point F) :
    difference F χ (orbit_refl F p) = 0 := by
  rw [difference, transport_unique F free _ (𝟙 _) (F.map_id_apply _ _), χ.map_id]

theorem difference_comp (free : Free F) (χ : Character J)
    {p q r : Point F} (h : Orbit F p q) (k : Orbit F q r) :
    difference F χ (orbit_trans F h k) = difference F χ h + difference F χ k := by
  unfold difference
  rw [transport_unique F free _ (transport F h ≫ transport F k) (by
    rw [F.map_comp_apply, transport_spec, transport_spec]), χ.map_comp]

def IsMarking (χ : Character J) (mark : Point F → Bit) : Prop :=
  ∀ {a b : J} (R : a ⟶ b) (q : F.obj a),
    mark ⟨b, F.map R q⟩ = mark ⟨a, q⟩ + χ.value R

def SeedCompatible (χ : Character J) (S : Set (Point F)) (ε : Point F → Bit) : Prop :=
  ∀ {a b : J} (R : a ⟶ b) (q : F.obj a),
    (⟨a, q⟩ : Point F) ∈ S → (⟨b, F.map R q⟩ : Point F) ∈ S →
    ε ⟨b, F.map R q⟩ = ε ⟨a, q⟩ + χ.value R

theorem marking_difference (_free : Free F) (χ : Character J)
    {mark : Point F → Bit} (hmark : IsMarking F χ mark)
    {p q : Point F} (h : Orbit F p q) : mark q = mark p + difference F χ h := by
  have e := hmark (transport F h) p.2
  simpa [transport_spec, difference] using e

def seed (S : Set (Point F)) (z : OrbitClass F) : Point F :=
  by
    classical
    exact if h : ∃ p, pointClass F p = z ∧ p ∈ S then Classical.choose h else Quotient.out z

theorem seed_class (S : Set (Point F)) (z : OrbitClass F) :
    pointClass F (seed F S z) = z := by
  classical
  unfold seed
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact Quotient.out_eq z

theorem seed_mem {S : Set (Point F)} {p : Point F} (hp : p ∈ S) :
    seed F S (pointClass F p) ∈ S := by
  classical
  unfold seed
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · exact False.elim (h ⟨p, rfl, hp⟩)

theorem seed_orbit (S : Set (Point F)) (p : Point F) :
    Orbit F (seed F S (pointClass F p)) p :=
  (class_eq_iff F).mp (seed_class F S _)

/-- Use the prescribed bit on a selected seed when present, and an arbitrary
bit otherwise; propagate along its unique actual transporting arrow. -/
def seededMarking (χ : Character J) (S : Set (Point F)) (ε : Point F → Bit) :
    Point F → Bit := fun p =>
  ε (seed F S (pointClass F p)) + difference F χ (seed_orbit F S p)

theorem seededMarking_isMarking (free : Free F) (χ : Character J)
    (S : Set (Point F)) (ε : Point F → Bit) :
    IsMarking F χ (seededMarking F χ S ε) := by
  intro a b R q
  let p : Point F := ⟨a, q⟩
  let r : Point F := ⟨b, F.map R q⟩
  have hpr : Orbit F p r := ⟨R, rfl⟩
  have hc : pointClass F r = pointClass F p := (class_eq_iff F).mpr (orbit_symm F hpr)
  have hs : seed F S (pointClass F r) = seed F S (pointClass F p) := congrArg _ hc
  have ht : Orbit F (seed F S (pointClass F p)) r :=
    orbit_trans F (seed_orbit F S p) hpr
  have hd : difference F χ ht = difference F χ (seed_orbit F S p) + χ.value R := by
    calc
      difference F χ ht = difference F χ (seed_orbit F S p) + difference F χ hpr :=
        difference_comp F free χ (seed_orbit F S p) hpr
      _ = difference F χ (seed_orbit F S p) + χ.value R := by
        unfold difference
        rw [transport_unique F free hpr R rfl]
  change seededMarking F χ S ε r = seededMarking F χ S ε p + χ.value R
  unfold seededMarking
  simpa only [hs, add_assoc] using congrArg (ε (seed F S (pointClass F p)) + ·) hd

theorem seededMarking_extends (_free : Free F) (χ : Character J)
    (S : Set (Point F)) (ε : Point F → Bit) (hε : SeedCompatible F χ S ε)
    {p : Point F} (hp : p ∈ S) : seededMarking F χ S ε p = ε p := by
  let s := seed F S (pointClass F p)
  have hs : s ∈ S := seed_mem F hp
  have h := seed_orbit F S p
  have hpt : (⟨p.1, F.map (transport F h) s.2⟩ : Point F) = p :=
    congrArg (Sigma.mk p.1) (transport_spec F h)
  have e := hε (transport F h) s.2 hs (hpt.symm ▸ hp)
  rw [hpt] at e
  exact e.symm

/-- The proof works even for an arbitrary prescribed subset; the finite
source export is an immediate restriction. No compactness theorem is used. -/
theorem exists_marking_extends_iff (free : Free F) (χ : Character J)
    (S : Set (Point F)) (ε : Point F → Bit) :
    (∃ mark, IsMarking F χ mark ∧ ∀ p ∈ S, mark p = ε p) ↔ SeedCompatible F χ S ε := by
  constructor
  · rintro ⟨mark, hmark, he⟩ a b R q hp hq
    rw [← he _ hp, ← he _ hq]
    exact hmark R q
  · intro hε
    exact ⟨seededMarking F χ S ε, seededMarking_isMarking F free χ S ε,
      fun _ hp => seededMarking_extends F free χ S ε hε hp⟩

theorem exists_marking (free : Free F) (χ : Character J) :
    ∃ mark, IsMarking F χ mark := by
  obtain ⟨mark, hmark, _⟩ := (exists_marking_extends_iff F free χ ∅ (fun _ => 0)).mpr (by
    intro a b R q hp
    exact False.elim hp)
  exact ⟨mark, hmark⟩

end
end CCO.RigidGroupoid.Phase.Abstract
