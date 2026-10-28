import CCO.FinitePackets.Geometry.Sigma
import CCO.FinitePackets.Geometry.MinimalCutBasic

/-! Crossing an actual minimal infinite cut. The equality/strict restriction
cases remain separate; general modularity and index factorization do not
acquire minimal-cut premises. No quotient-source theorem is used here. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

theorem sigma_bottom_spec : FiniteBottomSpec S (sigma S H (⊥ : ColourEq S i)) :=
  ⟨finiteIndex_sigma S H ⊥,fun _ h => sigma_greatest S H bot_le h⟩

theorem sigma_bottom_actual_finite_classes (x : X i) :
    Finite (CCO.RealHull.Geometry.ClassPoint S i (sigma S H (⊥ : ColourEq S i)) x) :=
  (finiteIndex_bottom_iff_finite_classes S _).mp (finiteIndex_sigma S H ⊥) x

/-- Any independently constructed greatest finite-class relation is the
same actual F; no second incompatible finite-bottom choice is introduced. -/
theorem finiteBottom_unique {F : ColourEq S i} (hF : FiniteBottomSpec S F) :
    F = sigma S H (⊥ : ColourEq S i) :=
  le_antisymm (sigma_greatest S H bot_le hF.1) (hF.2 _ (finiteIndex_sigma S H ⊥))

theorem actual_cut_lower_interval {E : ColourEq S i} (hE : MinimalInfiniteCut S E) :
    Set.Iic E = Set.Iic (E ⊓ sigma S H (⊥ : ColourEq S i)) ∪ {E} :=
  cut_lower_interval S hE (sigma_bottom_spec S H)

theorem cut_no_proper_finite_refinement {E J : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hJE : J ≤ E) (hfin : FiniteIndex S J E) : J = E := by
  by_contra hne
  exact hE.1 (finiteIndex_trans S ⊥ J E bot_le hJE
    (hE.2 J (lt_of_le_of_ne hJE hne)) hfin)

theorem cut_strict_interval_below_finite_part {E F J K : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F)
    (hJK : J < K) (hKE : K ≤ E) (hfin : FiniteIndex S J K) : K ≤ E ⊓ F := by
  have hne : K ≠ E := by
    intro he
    subst K
    exact hJK.ne (cut_no_proper_finite_refinement S hE hJK.le hfin)
  exact cut_proper_le_finite_part S hE hF (lt_of_le_of_ne hKE hne)

/-- C14: the restriction is finite by a literal injection of old classes.
Only its STRICT case is put below H; I=L=E is permitted. -/
theorem cut_finite_restriction {E F J K : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F)
    (hJK : J ≤ K) (hfin : FiniteIndex S J K) :
    FiniteIndex S (E ⊓ J) (E ⊓ K) ∧
      (E ⊓ J < E ⊓ K → E ⊓ K ≤ E ⊓ F) := by
  have hr := finiteIndex_restrict S E J K hfin
  exact ⟨hr,fun hlt => cut_strict_interval_below_finite_part S hE hF hlt inf_le_left hr⟩

/-- C16: this is the step which actually uses minimality. -/
theorem cut_crossing_meet {E F J K : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F)
    (hJK : J ≤ K) (hfin : FiniteIndex S J K) :
    K ⊓ ColourEq.join S H E J = K ⊓ ColourEq.join S H (E ⊓ F) J := by
  letI := ColourEq.lattice S H (i := i)
  rw [modular_path S H E J K hJK,modular_path S H (E ⊓ F) J K hJK]
  change J ⊔ (E ⊓ K) = J ⊔ ((E ⊓ F) ⊓ K)
  have hML : (E ⊓ F) ⊓ K ≤ E ⊓ K :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  by_cases he : E ⊓ J = E ⊓ K
  · have hLJ : E ⊓ K ≤ J := by rw [← he]; exact inf_le_right
    rw [sup_eq_left.mpr hLJ,sup_eq_left.mpr (hML.trans hLJ)]
  · have hlt : E ⊓ J < E ⊓ K :=
      lt_of_le_of_ne (inf_le_inf_left E hJK) he
    have hLH := (cut_finite_restriction S hE hF hJK hfin).2 hlt
    have hm : (E ⊓ F) ⊓ K = E ⊓ K :=
      le_antisymm hML (le_inf hLH inf_le_right)
    rw [hm]

theorem actual_cut_crossing_meet {E J K : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hJK : J ≤ K) (hfin : FiniteIndex S J K) :
    K ⊓ ColourEq.join S H E J =
      K ⊓ ColourEq.join S H (E ⊓ sigma S H (⊥ : ColourEq S i)) J :=
  cut_crossing_meet S H hE (sigma_bottom_spec S H) hJK hfin

/-- C18: F is absorbed by Sigma using its actual finite class index,
before applying the minimal-cut crossing identity. -/
theorem sigma_crossing {E J : ColourEq S i} (hE : MinimalInfiniteCut S E) :
    sigma S H J ⊓ ColourEq.join S H E J =
      ColourEq.join S H J (E ⊓ sigma S H (⊥ : ColourEq S i)) := by
  letI := ColourEq.lattice S H (i := i)
  let F := sigma S H (⊥ : ColourEq S i)
  have hF : FiniteBottomSpec S F := sigma_bottom_spec S H
  have hFsig : F ≤ sigma S H J := sigma_mono S H bot_le
  rw [cut_crossing_meet S H hE hF (le_sigma S H J) (finiteIndex_sigma S H J)]
  change sigma S H J ⊓ ((E ⊓ F) ⊔ J) = J ⊔ (E ⊓ F)
  rw [inf_eq_right.mpr (sup_le (inf_le_right.trans hFsig) (le_sigma S H J)),sup_comm]

end CCO.FinitePackets.Geometry
