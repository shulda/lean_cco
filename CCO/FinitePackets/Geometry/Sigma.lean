import CCO.FinitePackets.Geometry.RelativeIndices
import Mathlib.Data.Finset.Lattice.Fold

/-! The greatest finite-index coarsening in the FULL actual lattice.
Every finite-index assertion is about actual relative quotient types. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

noncomputable def finiteCoarsenings (J : ColourEq S i) : Finset (ColourEq S i) := by
  classical
  letI : Fintype (ColourEq S i) := Fintype.ofFinite _
  exact Finset.univ.filter (fun K => J ≤ K ∧ FiniteIndex S J K)

@[simp] theorem mem_finiteCoarsenings (J K : ColourEq S i) :
    K ∈ finiteCoarsenings S J ↔ J ≤ K ∧ FiniteIndex S J K := by
  classical
  simp only [finiteCoarsenings,Finset.mem_filter,Finset.mem_univ,true_and]

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

noncomputable def sigma (J : ColourEq S i) : ColourEq S i :=
  letI := ColourEq.lattice S H (i := i)
  J ⊔ (finiteCoarsenings S J).sup id

theorem le_sigma (J : ColourEq S i) : J ≤ sigma S H J := by
  letI := ColourEq.lattice S H (i := i)
  exact le_sup_left

theorem sigma_greatest {J K : ColourEq S i} (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) : K ≤ sigma S H J := by
  letI := ColourEq.lattice S H (i := i)
  have hK : K ≤ (finiteCoarsenings S J).sup id :=
    Finset.le_sup (f := id) ((mem_finiteCoarsenings S J K).mpr ⟨hJK,hfin⟩)
  exact hK.trans le_sup_right

theorem finiteIndex_sigma (J : ColourEq S i) : FiniteIndex S J (sigma S H J) := by
  classical
  letI := ColourEq.lattice S H (i := i)
  have step (s : Finset (ColourEq S i)) (hs : ∀ K ∈ s, J ≤ K ∧ FiniteIndex S J K) :
      FiniteIndex S J (J ⊔ s.sup id) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty,sup_bot_eq] using finiteIndex_self S J
    | @insert K s hKs ih =>
      have hK := hs K (Finset.mem_insert_self K s)
      have ht := ih (fun L hL => hs L (Finset.mem_insert_of_mem hL))
      have hj : J ⊔ (insert K s).sup id = K ⊔ (J ⊔ s.sup id) := by
        simp only [Finset.sup_insert,id_eq,sup_assoc,sup_comm,sup_left_comm]
      rw [hj]
      exact finiteIndex_join S H J K (J ⊔ s.sup id) hK.1 le_sup_left hK.2 ht
  exact step _ (fun K hK => (mem_finiteCoarsenings S J K).mp hK)

theorem sigma_eq_of_finiteIndex {J K : ColourEq S i} (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) : sigma S H J = sigma S H K := by
  apply le_antisymm
  · have hKsig : K ≤ sigma S H J := sigma_greatest S H hJK hfin
    exact sigma_greatest S H hKsig (finiteIndex_upper S hJK (finiteIndex_sigma S H J))
  · exact sigma_greatest S H (hJK.trans (le_sigma S H K))
      (finiteIndex_trans S J K (sigma S H K) hJK (le_sigma S H K)
        hfin (finiteIndex_sigma S H K))

@[simp] theorem sigma_idempotent (J : ColourEq S i) :
    sigma S H (sigma S H J) = sigma S H J :=
  (sigma_eq_of_finiteIndex S H (le_sigma S H J) (finiteIndex_sigma S H J)).symm

theorem sigma_mono : Monotone (sigma S H (i := i)) := by
  letI := ColourEq.lattice S H (i := i)
  intro J K hJK
  let T := sigma S H J
  have hJT : J ≤ T := le_sigma S H J
  have hfin : FiniteIndex S (K ⊓ T) T :=
    finiteIndex_upper S (le_inf hJK hJT) (finiteIndex_sigma S H J)
  have hjoin : FiniteIndex S K (K ⊔ T) := by
    intro x
    letI := hfin x
    exact Finite.of_equiv _ (classTransposition S H K T x)
  exact le_sup_right.trans (sigma_greatest S H le_sup_left hjoin)

theorem sigma_eq_iff_finiteIndex {J K : ColourEq S i} (hJK : J ≤ K) :
    sigma S H J = sigma S H K ↔ FiniteIndex S J K := by
  refine ⟨fun h => ?_,sigma_eq_of_finiteIndex S H hJK⟩
  have hK : K ≤ sigma S H J := by rw [h]; exact le_sigma S H K
  apply finiteIndex_lower S hK
  exact finiteIndex_sigma S H J

end CCO.FinitePackets.Geometry
