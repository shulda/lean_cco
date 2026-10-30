import CCO.UnaryFreshFrames.ClosureActions
import CCO.UnaryFreshFrames.Age
import CCO.UnaryFreshFrames.Examples.FiniteExtension
import Mathlib.Data.Set.Finite.Lattice

/-! Actual pure countable real set with one interpreted matching copy.
Only the forward bijection is named. Every original permutation acts on
both copies; no inverse unary symbol is added. -/
namespace CCO.PointGeneratedSAP.Examples.Matching
open UnaryFreshFrames UnaryFreshFrames.Structure

abbrev Point := Bool × ℕ
def real (n : ℕ) : Point := (false,n)
def hidden (n : ℕ) : Point := (true,n)

abbrev language : Language where
  Sorts := Bool
  Func := Unit
  Rel := Empty
  input _ := false
  output _ := true
  arity := Empty.elim
  argument := fun r => Empty.elim r

def model : Structure language Point where
  sort := Prod.fst
  func _ x := hidden x.2
  func_sort _ _ _ := rfl
  func_offsort := by
    rintro _ ⟨b,n⟩ hb
    cases b
    · exact False.elim (hb rfl)
    · rfl
  rel := fun r => Empty.elim r
  rel_sort := fun r => Empty.elim r

abbrev points (D : Set ℕ) : Set Point := {x | x.2 ∈ D}

theorem closure_reals (D : Set ℕ) : model.closure (real '' D) = points D := by
  apply Set.Subset.antisymm
  · apply model.closure_minimal
    · intro F x hx
      exact hx
    · rintro _ ⟨n,hn,rfl⟩
      exact hn
  · rintro ⟨b,n⟩ hn
    cases b
    · exact model.subset_closure _ ⟨n,hn,rfl⟩
    · exact model.closure_closed _ () (real n) (model.subset_closure _ ⟨n,hn,rfl⟩)

theorem closure_reals_finite {D : Set ℕ} (hD : D.Finite) :
    (model.closure (real '' D)).Finite := by
  rw [closure_reals]
  have he : points D = (real '' D) ∪ (hidden '' D) := by
    ext x
    rcases x with ⟨b,n⟩
    cases b <;> simp [points,real,hidden]
  rw [he]
  exact (hD.image real).union (hD.image hidden)

def perm (p : Equiv.Perm ℕ) : Equiv.Perm Point :=
  Equiv.prodCongr (Equiv.refl Bool) p

def permAut (p : Equiv.Perm ℕ) : model.Aut := by
  refine ⟨perm p,fun _ => rfl,fun _ _ => rfl,?_⟩
  intro r
  exact Empty.elim r

@[simp] theorem permAut_apply (p : Equiv.Perm ℕ) (b : Bool) (n : ℕ) :
    permAut p • (b,n) = (b,p n) := rfl

/-- Every full automorphism of the named expansion is induced by a UNIQUE
permutation of the original pure real set. -/
theorem full_aut_diagonal (g : model.Aut) :
    ∃! p : Equiv.Perm ℕ, ∀ (b : Bool) (n : ℕ), g • (b,n) = (b,p n) := by
  let p : Equiv.Perm ℕ := {
    toFun := fun n => (g • real n).2
    invFun := fun n => (g⁻¹ • real n).2
    left_inv := by
      intro n
      have hreal (a : model.Aut) (k : ℕ) : a • real k = real ((a • real k).2) := by
        apply Prod.ext
        · exact model.aut_sort a (real k)
        · rfl
      have he := congrArg Prod.snd (inv_smul_smul g (real n))
      rw [hreal g n] at he
      exact he
    right_inv := by
      intro n
      have hreal (a : model.Aut) (k : ℕ) : a • real k = real ((a • real k).2) := by
        apply Prod.ext
        · exact model.aut_sort a (real k)
        · rfl
      have he := congrArg Prod.snd (smul_inv_smul g (real n))
      rw [hreal g⁻¹ n] at he
      exact he }
  have hp (b : Bool) (n : ℕ) : g • (b,n) = (b,p n) := by
    cases b
    · apply Prod.ext
      · exact model.aut_sort g (real n)
      · rfl
    · have he := model.aut_func g () (real n)
      change g • hidden n = hidden ((g • real n).2) at he
      exact he
  refine ⟨p,hp,?_⟩
  intro q hq
  apply Equiv.ext
  intro n
  exact congrArg Prod.snd ((hq false n).symm.trans (hp false n))

/-- The actual original pure real structure is homogeneous: every finite
induced injection extends to a permutation of its original carrier. -/
theorem original_homogeneous {I : Type*} [Finite I] (f h : I → ℕ)
    (hf : Function.Injective f) (hh : Function.Injective h) :
    ∃ p : Equiv.Perm ℕ, ∀ i, p (f i) = h i := by
  apply UnaryFreshFrames.Examples.extend_equal_kernels
  intro i j
  exact hf.eq_iff.trans hh.eq_iff.symm

/-- Full original permutations fixing D give infinite orbits on EITHER
copy outside the entire point-generated closure, including D=empty. -/
theorem real_base_orbits (D : Set ℕ) (hD : D.Finite) (x : Point)
    (hx : x ∉ model.closure (real '' D)) :
    (orbitOver model.Aut (real '' D) x).Infinite := by
  classical
  intro hf
  obtain ⟨k,_,hk⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
    (hD.union (hf.image Prod.snd))
  have hn : x.2 ∉ D := by simpa only [closure_reals,points,Set.mem_ofPred_eq] using hx
  let g := permAut (Equiv.swap x.2 k)
  have hfix : ∀ a ∈ real '' D, g • a = a := by
    rintro _ ⟨n,hnD,rfl⟩
    change (false,Equiv.swap x.2 k n) = real n
    rw [Equiv.swap_apply_of_ne_of_ne (fun he : n = x.2 => hn (he ▸ hnD))
      (fun he : n = k => hk (Or.inl (he ▸ hnD)))]
    rfl
  have hmove : g • x = (x.1,k) := by
    rcases x with ⟨b,n⟩
    change (b,Equiv.swap n k n) = _
    simp
  have hm : (x.1,k) ∈ orbitOver model.Aut (real '' D) x :=
    (mem_orbitOver_iff model.Aut).mpr ⟨g,hfix,hmove⟩
  exact hk (Or.inr ⟨(x.1,k),hm,rfl⟩)

theorem term_nonreal {i j : language.Sorts} (hi : i ≠ false) (t : Term language i j) : i = j := by
  induction t with
  | id => rfl
  | func F t ih => exact False.elim (hi ih)

theorem no_inverse_term : ¬ Nonempty (Term language true false) := by
  rintro ⟨t⟩
  exact Bool.noConfusion (term_nonreal (by decide) t)

def orphan (n : ℕ) : model.Piece where
  points := {hidden n}
  finite := Set.finite_singleton _
  closed := by
    rintro F x rfl
    rfl

def pair (n : ℕ) : model.Piece where
  points := {real n,hidden n}
  finite := (Set.finite_singleton _).insert _
  closed := by
    rintro F x (rfl | rfl) <;> exact Or.inr rfl

theorem orphan_not_point_generated (n : ℕ) :
    ¬ ∃ D : Set ℕ, (orphan n).points = model.closure (real '' D) := by
  rintro ⟨D,hD⟩
  have hh : hidden n ∈ model.closure (real '' D) := hD ▸ (show hidden n ∈ (orphan n).points from rfl)
  have hn : n ∈ D := by simpa only [closure_reals,points,Set.mem_ofPred_eq,hidden] using hh
  have hr : real n ∈ (orphan n).points := hD ▸ model.subset_closure _ ⟨n,hn,rfl⟩
  exact Bool.noConfusion (congrArg Prod.fst hr)

theorem operation_injective_real {x y : Point} (hx : model.sort x = false)
    (hy : model.sort y = false) (he : model.func () x = model.func () y) : x = y := by
  have hn : x.2 = y.2 := by
    change hidden x.2 = hidden y.2 at he
    exact (Prod.mk.inj he).2
  exact Prod.ext (hx.trans hy.symm) hn

/-- The ACTUAL hereditary unary age fails SAP over an orphan hidden base:
its two real preimages must coincide in every induced amalgam. -/
theorem not_hereditary_SAP : ¬ model.AgeSAP := by
  intro sap
  let A := orphan 0
  let B := pair 0
  let s : A.Embedding B.points := Piece.Embedding.inclusion (fun _ hx => Or.inr hx)
  obtain ⟨D,l,r,hbase,hstrong⟩ := sap A B B s s
  let a : A.points := ⟨hidden 0,rfl⟩
  let x : B.points := ⟨real 0,Or.inl rfl⟩
  have he : l.point (B.func () x) = r.point (B.func () x) := hbase a
  have hp : l.point x = r.point x := operation_injective_real (l.sort_eq x)
    (r.sort_eq x) ((l.func_eq () x).symm.trans (he.trans (r.func_eq () x)))
  obtain ⟨b,hb,_⟩ := hstrong x x hp
  have heq : b.val = real 0 := hb
  have hhidden : b.val = hidden 0 := b.property
  exact Bool.noConfusion (congrArg Prod.fst (heq.symm.trans hhidden))

end CCO.PointGeneratedSAP.Examples.Matching
