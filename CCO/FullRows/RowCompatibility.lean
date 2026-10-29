import CCO.FullRows.Rows

/-! The exact simultaneous FULL-row criterion. Only off-diagonal holes
are reflected. Diagonals and recorded pairs have no extra equations. -/
universe u v
namespace CCO.FullRows
variable {I : Type u} {K : Type v} [CommGroup K]
variable (hsquare : ∀ g : K, g * g = 1)
include hsquare

theorem solve_shift (a c b r : K) : a * (c * b) = r ↔ c = r * a * b := by
  constructor
  · intro h
    calc
      c = (a * (c * b)) * a * b := by
        symm
        calc
          _ = c * ((a*a)*(b*b)) := by ac_rfl
          _ = c := by rw [hsquare,hsquare,one_mul,mul_one]
      _ = r * a * b := by rw [h]
  · intro h
    rw [h]
    calc
      _ = r * ((a*a)*(b*b)) := by ac_rfl
      _ = r := by rw [hsquare,hsquare,one_mul,mul_one]

theorem rowImage_eq_iff_forced (s : Structural I K) (C : Matrix I K)
    (i : I) (f r : Row I K) :
    rowImage s C i f = r ↔ ∀ j, C i j = r (s.sigma j) * f j * s.offset i := by
  constructor
  · intro h j
    apply (solve_shift hsquare _ _ _ _).mp
    simpa only [rowImage_apply_sigma] using congrFun h (s.sigma j)
  · intro h
    funext j
    obtain ⟨k,rfl⟩ := s.sigma.surjective j
    rw [rowImage_apply_sigma]
    exact (solve_shift hsquare _ _ _ _).mpr (h k)

theorem compatibility_necessary (s : Structural I K) (R : I → I → Prop)
    (T : I → Finset (Row I K)) (r : I → Row I K → Row I K)
    (C : Matrix I K) (hC : Legal R C) (hreal : Realizes s T r C) :
    RC1 s T r ∧ RC2 s R T r := by
  have hf : ∀ i f, f ∈ T i → ∀ j, C i j = forced s r i f j := by
    intro i f hf j
    exact (rowImage_eq_iff_forced hsquare s C i f (r i f)).mp (hreal i f hf) j
  constructor
  · intro i f hfi f' hfi'
    funext j
    exact (hf i f hfi j).symm.trans (hf i f' hfi' j)
  · intro i j hij hr f hfi f' hfj
    exact (hf i f hfi j).symm.trans ((hC i j hij hr).trans (hf j f' hfj i))

theorem compatibility_sufficient (s : Structural I K) (R : I → I → Prop)
    (hR : Symmetric R) (T : I → Finset (Row I K))
    (r : I → Row I K → Row I K) (h1 : RC1 s T r) (h2 : RC2 s R T r) :
    ∃ C : Matrix I K, Legal R C ∧ Realizes s T r C := by
  classical
  let A : I → Row I K := fun i =>
    if h : (T i).Nonempty then forced s r i (Classical.choose h) else 1
  have hA : ∀ i f, f ∈ T i → A i = forced s r i f := by
    intro i f hf
    have hi : (T i).Nonempty := ⟨f,hf⟩
    dsimp [A]
    rw [dif_pos hi]
    exact h1 i _ (Classical.choose_spec hi) f hf
  let C : Matrix I K := fun i j =>
    if (T i).Nonempty then A i j
    else if i ≠ j ∧ ¬R i j ∧ (T j).Nonempty then A j i else 1
  refine ⟨C,?_,?_⟩
  · intro i j hij hr
    have hji : j ≠ i := Ne.symm hij
    have hrji : ¬R j i := fun h => hr (hR h)
    by_cases hi : (T i).Nonempty <;> by_cases hj : (T j).Nonempty
    · obtain ⟨f,hf⟩ := hi
      obtain ⟨f',hf'⟩ := hj
      have ha := congrFun (hA i f hf) j
      have hb := congrFun (hA j f' hf') i
      simpa only [C,if_pos (show (T i).Nonempty from ⟨f,hf⟩),
        if_pos (show (T j).Nonempty from ⟨f',hf'⟩)] using
        ha.trans ((h2 i j hij hr f hf f' hf').trans hb.symm)
    · simp [C,hi,hj,hij,hji,hr,hrji]
    · simp [C,hi,hj,hij,hji,hr,hrji]
    · simp [C,hi,hj]
  · intro i f hf
    apply (rowImage_eq_iff_forced hsquare s C i f (r i f)).mpr
    intro j
    have hi : (T i).Nonempty := ⟨f,hf⟩
    simpa only [C,if_pos hi,forced] using congrFun (hA i f hf) j

theorem row_compatibility_iff (s : Structural I K) (R : I → I → Prop)
    (hR : Symmetric R) (T : I → Finset (Row I K))
    (r : I → Row I K → Row I K) :
    (∃ C : Matrix I K, Legal R C ∧ Realizes s T r C) ↔ RC1 s T r ∧ RC2 s R T r := by
  constructor
  · rintro ⟨C,hC,hr⟩
    exact compatibility_necessary hsquare s R T r C hC hr
  · rintro ⟨h1,h2⟩
    exact compatibility_sufficient hsquare s R hR T r h1 h2

/-- One specified actual row over each recorded-clique index, simultaneously. -/
theorem recorded_clique_zeroing (s : Structural I K) (R : I → I → Prop)
    (hR : Symmetric R) (J : Set I) (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → R i j)
    (f : I → Row I K) :
    ∃ C : Matrix I K, Legal R C ∧
      (∀ i ∈ J, rowImage s C i (f i) = 1) ∧
      (∀ i ∈ J, ∀ j, C i j = f i j * s.offset i) := by
  classical
  let T : I → Finset (Row I K) := fun i => if i ∈ J then {f i} else ∅
  have hm : ∀ i a, a ∈ T i ↔ i ∈ J ∧ a = f i := by
    intro i a
    by_cases hi : i ∈ J <;> simp [T,hi]
  have h1 : RC1 s T (fun _ _ => 1) := by
    intro i a ha b hb
    rcases (hm i a).mp ha with ⟨_,rfl⟩
    rcases (hm i b).mp hb with ⟨_,rfl⟩
    rfl
  have h2 : RC2 s R T (fun _ _ => 1) := by
    intro i j hij hr a ha b hb
    exact (hr (hJ i ((hm i a).mp ha).1 j ((hm j b).mp hb).1 hij)).elim
  obtain ⟨C,hC,hreal⟩ := compatibility_sufficient hsquare s R hR T (fun _ _ => 1) h1 h2
  have hz : ∀ i ∈ J, rowImage s C i (f i) = 1 := by
    intro i hi
    exact hreal i (f i) ((hm i (f i)).mpr ⟨hi,rfl⟩)
  refine ⟨C,hC,hz,?_⟩
  intro i hi j
  have he := (rowImage_eq_iff_forced hsquare s C i (f i) 1).mp (hz i hi) j
  simpa only [Pi.one_apply,one_mul] using he

/-- Complete zero-row sources are the special case `f=1`, including empty J. -/
theorem zero_row_requests (s : Structural I K) (R : I → I → Prop)
    (hR : Symmetric R) (J : Set I) (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → R i j) :
    ∃ C : Matrix I K, Legal R C ∧
      (∀ i ∈ J, rowImage s C i 1 = 1) ∧
      (∀ i ∈ J, ∀ j, C i j = s.offset i) := by
  obtain ⟨C,hC,hz,hf⟩ := recorded_clique_zeroing hsquare s R hR J hJ (fun _ => 1)
  exact ⟨C,hC,hz,by simpa using hf⟩

end CCO.FullRows
