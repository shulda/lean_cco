import CCO.ExactEPGeometry.ExactMeetSupport

/-!
# B062 C47–C50: original FULL RAW-exact finite meet support

Every original FullExact relation has a REAL nonempty RAW exact
presentation. The certified exact-family support theorem therefore
preserves all finite FULL-exact relation intersections whose OLD
simultaneous intersection is nonempty. The displayed type supports
are existential over actual current points.

The binary corollary is the precise support-meet equation used on
original exact equivalences: their old common diagonal supplies the
nonemptiness guard. It is NOT extended to empty intersections of
unrelated diversity atoms.
-/

universe u v w

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}
variable (P : UnaryReduct S T)
variable (hMeet : ExactMeetSupport S T P)

/-- C47–C50 actual finite-meet equation for FULL equality-inclusive
exact relations. The only old nonemptiness premise is for the ENTIRE
finite family, not independent nonemptiness of its factors. All
presentations are obtained from genuine source FullExact proofs, not
postulated as new providers. -/
theorem fullExact_family_support_iff
    {F : Type} [Fintype F] {i j : κ}
    (R : F → TRel X (P.parent i) (P.parent j))
    (hExact : ∀ f : F, FullExact S (R f))
    (hOld : ∃ a : X (P.parent i), ∃ b : X (P.parent j),
      ∀ f : F, R f a b) :
    (∃ x : Y i, ∃ y : Y j,
      ∀ f : F, R f (P.point i x) (P.point j y)) ↔
      ∀ f : F, ∃ x : Y i, ∃ y : Y j,
        R f (P.point i x) (P.point j y) := by
  classical
  let D : F → RawExact.NonemptyExact S (P.parent i) (P.parent j) :=
    fun f => Classical.choose (hExact f)
  have hD (f : F) :
      RawExact.evaluate S (D f).words = R f :=
    Classical.choose_spec (hExact f)
  constructor
  · rintro ⟨x,y,hAll⟩ f
    exact ⟨x,y,hAll f⟩
  · intro hEach
    have hOldD :
        ∃ a : X (P.parent i), ∃ b : X (P.parent j),
          ∀ f : F, RawExact.evaluate S (D f).words a b := by
      obtain ⟨a,b,hAll⟩ := hOld
      refine ⟨a,b,?_⟩
      intro f
      rw [hD f]
      exact hAll f
    have hEachD :
        ∀ f : F, ∃ x : Y i, ∃ y : Y j,
          RawExact.evaluate S (D f).words (P.point i x) (P.point j y) := by
      intro f
      obtain ⟨x,y,hxy⟩ := hEach f
      refine ⟨x,y,?_⟩
      rw [hD f]
      exact hxy
    obtain ⟨x,y,hAll⟩ := hMeet.meets D hOldD hEachD
    refine ⟨x,y,?_⟩
    intro f
    rw [← hD f]
    exact hAll f

/-- Source N06 binary support intersection identity for two original
FULL-exact relations on the SAME actual old pair of named sorts. If
the relations are original exact equivalences on the original single
sort, their common diagonal gives `hOld` automatically. This theorem
does not assert the formula for empty old diversity-atom intersections. -/
theorem fullExact_pair_support_inter_iff
    {i j : κ}
    (R U : TRel X (P.parent i) (P.parent j))
    (hR : FullExact S R) (hU : FullExact S U)
    (hOld : TRel.Nonempty (fun a b => R a b ∧ U a b)) :
    (∃ x : Y i, ∃ y : Y j,
        R (P.point i x) (P.point j y) ∧
        U (P.point i x) (P.point j y)) ↔
      (∃ x : Y i, ∃ y : Y j,
        R (P.point i x) (P.point j y)) ∧
      (∃ x : Y i, ∃ y : Y j,
        U (P.point i x) (P.point j y)) := by
  let L : Bool → TRel X (P.parent i) (P.parent j) :=
    fun b => if b then R else U
  have hExact : ∀ b : Bool, FullExact S (L b) := by
    intro b
    cases b with
    | false => exact hU
    | true => exact hR
  have hOldL :
      ∃ a : X (P.parent i), ∃ b : X (P.parent j),
        ∀ f : Bool, L f a b := by
    obtain ⟨a,b,hRa,hUa⟩ := hOld
    refine ⟨a,b,?_⟩
    intro f
    cases f with
    | false => exact hUa
    | true => exact hRa
  have hIff := fullExact_family_support_iff P hMeet L hExact hOldL
  constructor
  · rintro ⟨x,y,hRx,hUx⟩
    exact ⟨⟨x,y,hRx⟩,⟨x,y,hUx⟩⟩
  · rintro ⟨⟨x,y,hRx⟩,⟨x',y',hUy⟩⟩
    have hEachL : ∀ f : Bool, ∃ a : Y i, ∃ b : Y j,
        L f (P.point i a) (P.point j b) := by
      intro f
      cases f with
      | false => exact ⟨x',y',hUy⟩
      | true => exact ⟨x,y,hRx⟩
    obtain ⟨a,b,hAll⟩ := hIff.mpr hEachL
    exact ⟨a,b,hAll true,hAll false⟩

end
end CCO.ExactEPGeometry
