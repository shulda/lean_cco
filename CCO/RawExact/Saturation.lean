import CCO.RawExact.MixedJoins
import CCO.GroupQuotient

/-!
# B002 C14 and C19: RAW kernel saturation and quotient requests

The relations here are actual, equality-inclusive predicates. These
statements are independent of exact Helly, SAP and semantic CCO. Exact
word-presentability of the saturated product will depend on C09.
-/

universe u v

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}

/-- Saturate an actual typed pair relation by two genuine equivalences. -/
def saturate {i j : ι}
    (J : TRel X i i) (R : TRel X i j) (K : TRel X j j) :
    TRel X i j :=
  TRel.comp (TRel.comp J R) K

theorem typed_equiv_comp_self {i : ι} (J : TRel X i i)
    (hJ : RawSymmetric.EquivRel J) :
    TRel.comp J J = J := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, hxz, hzy⟩
    exact hJ.trans x z y hxz hzy
  · intro hxy
    exact ⟨y, hxy, hJ.refl y⟩

/-- Neither left nor right extra saturation changes a full kernel
product: J;(J;R;K) = (J;R;K);K = J;R;K. -/
theorem saturate_idempotent {i j : ι}
    (J : TRel X i i) (R : TRel X i j) (K : TRel X j j)
    (hJ : RawSymmetric.EquivRel J)
    (hK : RawSymmetric.EquivRel K) :
    TRel.comp J (saturate J R K) = saturate J R K ∧
    TRel.comp (saturate J R K) K = saturate J R K := by
  constructor
  · calc
      TRel.comp J (saturate J R K) =
          TRel.comp (TRel.comp J (TRel.comp J R)) K :=
        (TRel.comp_assoc J (TRel.comp J R) K).symm
      _ = TRel.comp (TRel.comp (TRel.comp J J) R) K := by
        rw [← TRel.comp_assoc J J R]
      _ = saturate J R K := by
        rw [typed_equiv_comp_self J hJ]
        rfl
  · calc
      TRel.comp (saturate J R K) K =
          TRel.comp (TRel.comp J R) (TRel.comp K K) :=
        TRel.comp_assoc (TRel.comp J R) K K
      _ = saturate J R K := by
        rw [typed_equiv_comp_self K hK]
        rfl

/-- The full orbit pullback from B001 is literally the typed
J;a;K product; there is no abstract quotient-colour assumption. -/
theorem saturate_kernels {i j : ι} {Q R : Type*}
    (τ : X i → Q) (σ : X j → R) (O : TRel X i j) :
    saturate (GroupActions.kernel τ) O (GroupActions.kernel σ) =
      GroupActions.saturation τ σ O := by
  funext x y
  apply propext
  constructor
  · rintro ⟨v, ⟨u, hu, hO⟩, hv⟩
    exact ⟨u, v, hu, hO, hv⟩
  · rintro ⟨u, v, hu, hO, hv⟩
    exact ⟨v, ⟨u, hu, hO⟩, hv⟩

/-- C14's actual pair-orbit identity for arbitrary equivariant
quotient maps, with no chosen section or faithful group action. -/
theorem equivariant_orbit_pullback
    {i j : ι} {G Q R : Type*} [Group G]
    [MulAction G (X i)] [MulAction G (X j)]
    [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (a : X i) (b : X j) :
    GroupActions.pullback τ σ
      (GroupActions.orbital (G := G) (τ a) (σ b)) =
      saturate (GroupActions.kernel τ)
        (GroupActions.orbital (G := G) a b)
        (GroupActions.kernel σ) := by
  calc
    GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)) =
      GroupActions.saturation τ σ
        (GroupActions.orbital (G := G) a b) :=
      GroupActions.orbital_pullback τ σ equivτ equivσ a b
    _ = saturate (GroupActions.kernel τ)
        (GroupActions.orbital (G := G) a b)
        (GroupActions.kernel σ) :=
      (saturate_kernels τ σ (GroupActions.orbital (G := G) a b)).symm

/-- Saturating on the right with an actual equivalence twice
changes nothing: the main algebraic ingredient of C19 requests. -/
theorem right_request_saturated {i j : ι}
    (R : TRel X i j) (K : TRel X j j)
    (hK : RawSymmetric.EquivRel K) :
    TRel.comp (TRel.comp R K) K = TRel.comp R K := by
  calc
    TRel.comp (TRel.comp R K) K =
      TRel.comp R (TRel.comp K K) := TRel.comp_assoc R K K
    _ = TRel.comp R K := by rw [typed_equiv_comp_self K hK]

/-- The saturated request of a real colour a can use equality on its
left with no change. -/
theorem identity_left_request {i j : ι}
    (R : TRel X i j) (K : TRel X j j) :
    saturate (TRel.ident X i) R K = TRel.comp R K := by
  change TRel.comp (TRel.comp (TRel.ident X i) R) K =
    TRel.comp R K
  rw [TRel.ident_comp]

end CCO.RawExact
