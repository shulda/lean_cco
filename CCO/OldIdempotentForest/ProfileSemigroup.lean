import CCO.GuardedTwoRoot.TypedPrefixBounds
import CCO.RawOrbitals

/-!
# The actual finite typed positive-profile semigroup

Positive states are precisely the accepted nonempty reachable profiles,
with both endpoint sorts retained. A separate absorbing zero records type
mismatches. No STRONG identity or logical equality atom is adjoined.
-/

universe u v w r
namespace CCO.OldIdempotentForest
open CCO.GuardedTwoRoot
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

abbrev ReachableProfile := TypedPrefix.ReachableState S

namespace ReachableProfile
variable {S}
def source (p : ReachableProfile S) : ι := p.val.1
def target (p : ReachableProfile S) : ι := p.val.2.1
def menu (p : ReachableProfile S) : S.Menu p.source p.target := p.val.2.2.val
theorem nonempty (p : ReachableProfile S) : p.menu.Nonempty := p.val.2.2.property
theorem reachable (p : ReachableProfile S) :
    ∃ w : PositiveWord S p.source p.target, PositiveWord.profile S w = p.menu := p.property
def Compatible (p q : ReachableProfile S) : Prop := p.target = q.source
end ReachableProfile

inductive TypedProfileState where
  | zero
  | positive (profile : ReachableProfile S)

namespace TypedProfileState
variable {S}

def optionEquiv : TypedProfileState S ≃ Option (ReachableProfile S) where
  toFun
    | .zero => none
    | .positive p => some p
  invFun
    | none => .zero
    | some p => .positive p
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Finite (TypedProfileState S) := Finite.of_equiv _ optionEquiv.symm
instance : Nonempty (TypedProfileState S) := ⟨.zero⟩
noncomputable instance : Fintype (TypedProfileState S) := Fintype.ofFinite _

/-- The stipulated cardinal counts only actual positive reachable
profiles, plus the one absorbing mismatch state. -/
theorem card_eq : Nat.card (TypedProfileState S) = Nat.card (ReachableProfile S) + 1 := by
  rw [Nat.card_congr (optionEquiv (S := S)),Finite.card_option]

@[simp] theorem positive_ne_zero (p : ReachableProfile S) :
    (positive p : TypedProfileState S) ≠ zero := by intro h; cases h

end TypedProfileState

variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
include H

/-- Every nonempty actual palette is serial at its source sort. -/
theorem palette_serial {i j : ι} (P : S.Menu i j) (hP : P.Nonempty) :
    TRel.Serial (S.menuRel P) := by
  apply TRel.invariant_serial (S.menuRel P)
    (S.original_sort_transitive_of_homogeneous H i)
  · rintro g x y ⟨a,ha,hxy⟩
    exact ⟨a,ha,(S.colourInvariant_of_homogeneous H g x y).trans hxy⟩
  · obtain ⟨a,ha⟩ := hP
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,a,ha,hxy⟩

/-- Every nonempty actual palette is coserial at its target sort. -/
theorem palette_coserial {i j : ι} (P : S.Menu i j) (hP : P.Nonempty) :
    TRel.Coserial (S.menuRel P) := by
  apply TRel.invariant_coserial (S.menuRel P)
    (S.original_sort_transitive_of_homogeneous H j)
  · rintro g x y ⟨a,ha,hxy⟩
    exact ⟨a,ha,(S.colourInvariant_of_homogeneous H g x y).trans hxy⟩
  · obtain ⟨a,ha⟩ := hP
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,a,ha,hxy⟩

include sap
/-- The actual complete-pair SAP theorem separates all three vertices
of the compatible fork. No abstract nonzero-product provider is assumed. -/
theorem compatible_product_nonempty {i j k : ι}
    (P : S.Menu i j) (Q : S.Menu j k) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    (S.product P Q).Nonempty :=
  S.product_nonempty_of_point_gluing (S.realPointGluing_of_SAP H sap) hP hQ

/-- Compatible products remain ACTUALLY reachable: concatenate the
original positive witnesses, retaining their genuine sort boundary. -/
def composeReachable (p q : ReachableProfile S) (h : p.Compatible q) :
    ReachableProfile S := by
  rcases p with ⟨⟨i,j,⟨P,hP⟩⟩,hp⟩
  rcases q with ⟨⟨j',k,⟨Q,hQ⟩⟩,hq⟩
  change j = j' at h
  subst j'
  refine ⟨⟨i,k,⟨S.product P Q,compatible_product_nonempty S H sap P Q hP hQ⟩⟩,?_⟩
  obtain ⟨left,hleft⟩ := hp
  obtain ⟨right,hright⟩ := hq
  exact ⟨PositiveWord.append S left right,by
    rw [PositiveWord.profile_append_of_SAP S H sap,hleft,hright]⟩

@[simp] theorem composeReachable_source (p q : ReachableProfile S) (h : p.Compatible q) :
    (composeReachable S H sap p q h).source = p.source := by
  rcases p with ⟨⟨i,j,⟨P,hP⟩⟩,hp⟩
  rcases q with ⟨⟨j',k,⟨Q,hQ⟩⟩,hq⟩
  change j = j' at h
  subst j'
  rfl

@[simp] theorem composeReachable_target (p q : ReachableProfile S) (h : p.Compatible q) :
    (composeReachable S H sap p q h).target = q.target := by
  rcases p with ⟨⟨i,j,⟨P,hP⟩⟩,hp⟩
  rcases q with ⟨⟨j',k,⟨Q,hQ⟩⟩,hq⟩
  change j = j' at h
  subst j'
  rfl

def profileMul : TypedProfileState S → TypedProfileState S → TypedProfileState S := by
  classical
  exact fun x y => match x,y with
    | .positive p,.positive q => if h : p.Compatible q then
        .positive (composeReachable S H sap p q h) else .zero
    | _,_ => .zero

@[simp] theorem profileMul_zero_left (x : TypedProfileState S) :
    profileMul S H sap .zero x = .zero := by cases x <;> rfl
@[simp] theorem profileMul_zero_right (x : TypedProfileState S) :
    profileMul S H sap x .zero = .zero := by cases x <;> rfl

theorem profileMul_compatible (p q : ReachableProfile S) (h : p.Compatible q) :
    profileMul S H sap (.positive p) (.positive q) =
      .positive (composeReachable S H sap p q h) := by
  simp only [profileMul,dif_pos h]

theorem profileMul_incompatible (p q : ReachableProfile S) (h : ¬ p.Compatible q) :
    profileMul S H sap (.positive p) (.positive q) = .zero := by
  simp only [profileMul,dif_neg h]

theorem composeReachable_assoc (p q t : ReachableProfile S)
    (hpq : p.Compatible q) (hqt : q.Compatible t) :
    composeReachable S H sap (composeReachable S H sap p q hpq) t
        (by simpa only [ReachableProfile.Compatible,composeReachable_target] using hqt) =
      composeReachable S H sap p (composeReachable S H sap q t hqt)
        (by simpa only [ReachableProfile.Compatible,composeReachable_source] using hpq) := by
  rcases p with ⟨⟨i,j,⟨P,hP⟩⟩,hp⟩
  rcases q with ⟨⟨j',k,⟨Q,hQ⟩⟩,hq⟩
  rcases t with ⟨⟨k',l,⟨R,hR⟩⟩,ht⟩
  change j = j' at hpq
  change k = k' at hqt
  subst j'
  subst k'
  apply Subtype.ext
  change (⟨i,l,⟨S.product (S.product P Q) R,
    compatible_product_nonempty S H sap _ _
      (compatible_product_nonempty S H sap P Q hP hQ) hR⟩⟩ : TypedPrefix.State S) =
    ⟨i,l,⟨S.product P (S.product Q R),compatible_product_nonempty S H sap _ _ hP
      (compatible_product_nonempty S H sap Q R hQ hR)⟩⟩
  simp only [Sigma.mk.injEq,heq_eq_eq,true_and,Subtype.mk.injEq]
  exact S.product_assoc_of_edge_gluing (S.realEdgeGluing_of_SAP H sap) P Q R

theorem profileMul_assoc (x y z : TypedProfileState S) :
    profileMul S H sap (profileMul S H sap x y) z =
      profileMul S H sap x (profileMul S H sap y z) := by
  classical
  cases x with
  | zero => simp only [profileMul_zero_left]
  | positive p =>
    cases y with
    | zero => simp only [profileMul_zero_left,profileMul_zero_right]
    | positive q =>
      cases z with
      | zero => simp only [profileMul_zero_right]
      | positive t =>
        by_cases hpq : p.Compatible q
        · by_cases hqt : q.Compatible t
          · rw [profileMul_compatible S H sap p q hpq,
              profileMul_compatible S H sap q t hqt]
            rw [profileMul_compatible S H sap _ t
              (by simpa only [ReachableProfile.Compatible,composeReachable_target] using hqt)]
            rw [profileMul_compatible S H sap p _
              (by simpa only [ReachableProfile.Compatible,composeReachable_source] using hpq)]
            exact congrArg TypedProfileState.positive (composeReachable_assoc S H sap p q t hpq hqt)
          · rw [profileMul_compatible S H sap p q hpq,
              profileMul_incompatible S H sap q t hqt,profileMul_zero_right]
            apply profileMul_incompatible
            simpa only [ReachableProfile.Compatible,composeReachable_target] using hqt
        · rw [profileMul_incompatible S H sap p q hpq,profileMul_zero_left]
          by_cases hqt : q.Compatible t
          · rw [profileMul_compatible S H sap q t hqt]
            symm
            apply profileMul_incompatible
            simpa only [ReachableProfile.Compatible,composeReachable_source] using hpq
          · rw [profileMul_incompatible S H sap q t hqt,profileMul_zero_right]

/-- Actual semigroup instance for the receiving forest theorem. It has
an absorbing zero and deliberately has no asserted identity instance. -/
def profileSemigroup : Semigroup (TypedProfileState S) where
  mul := profileMul S H sap
  mul_assoc := profileMul_assoc S H sap

/-- The exact strong profile of this ORIGINAL word, with no replacement
presentation chosen. -/
def wordProfile {i j : ι} (word : PositiveWord S i j) : ReachableProfile S :=
  ⟨⟨i,j,⟨PositiveWord.profile S word,PositiveWord.profile_nonempty_of_SAP S H sap word⟩⟩,
    word,rfl⟩

@[simp] theorem wordProfile_source {i j : ι} (word : PositiveWord S i j) :
    (wordProfile S H sap word).source = i := rfl
@[simp] theorem wordProfile_target {i j : ι} (word : PositiveWord S i j) :
    (wordProfile S H sap word).target = j := rfl
@[simp] theorem wordProfile_menu {i j : ι} (word : PositiveWord S i j) :
    (wordProfile S H sap word).menu = PositiveWord.profile S word := rfl

theorem compose_wordProfile {i j k : ι}
    (first : PositiveWord S i j) (second : PositiveWord S j k) :
    composeReachable S H sap (wordProfile S H sap first) (wordProfile S H sap second) rfl =
      wordProfile S H sap (PositiveWord.append S first second) := by
  apply Subtype.ext
  change (⟨i,k,⟨S.product (PositiveWord.profile S first) (PositiveWord.profile S second),_⟩⟩ :
    TypedPrefix.State S) = ⟨i,k,⟨PositiveWord.profile S (PositiveWord.append S first second),_⟩⟩
  simp only [Sigma.mk.injEq,heq_eq_eq,true_and,Subtype.mk.injEq]
  exact (PositiveWord.profile_append_of_SAP S H sap first second).symm

theorem positive_idempotent_same_sort (p : ReachableProfile S)
    (h : profileMul S H sap (.positive p) (.positive p) = .positive p) :
    p.source = p.target := by
  classical
  by_contra hn
  have hi : ¬ p.Compatible p := fun he => hn he.symm
  rw [profileMul_incompatible S H sap p p hi] at h
  cases h

/-- A nonzero semigroup idempotent is precisely a nonempty reachable
same-sort diversity idempotent. No RAW equality or monolith is substituted. -/
theorem nonzero_idempotent_profile (x : TypedProfileState S)
    (hn : x ≠ .zero) (hx : profileMul S H sap x x = x) :
    ∃ (i : ι) (P : S.Menu i i) (hP : P.Nonempty)
      (hReach : ∃ word : PositiveWord S i i, PositiveWord.profile S word = P),
      x = .positive ⟨⟨i,i,⟨P,hP⟩⟩,hReach⟩ ∧ S.product P P = P := by
  cases x with
  | zero => exact False.elim (hn rfl)
  | positive p =>
    have hs := positive_idempotent_same_sort S H sap p hx
    rcases p with ⟨⟨i,j,⟨P,hP⟩⟩,hReach⟩
    change i = j at hs
    subst j
    have hc : ReachableProfile.Compatible
        (⟨⟨i,i,⟨P,hP⟩⟩,hReach⟩ : ReachableProfile S) ⟨⟨i,i,⟨P,hP⟩⟩,hReach⟩ := rfl
    rw [profileMul_compatible S H sap _ _ hc] at hx
    have he := congrArg Subtype.val (TypedProfileState.positive.inj hx)
    change (⟨i,i,⟨S.product P P,compatible_product_nonempty S H sap P P hP hP⟩⟩ :
      TypedPrefix.State S) = ⟨i,i,⟨P,hP⟩⟩ at he
    have hProd : S.product P P = P := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and,Subtype.mk.injEq] using he
    exact ⟨i,P,hP,hReach,rfl,hProd⟩

end
end CCO.OldIdempotentForest
