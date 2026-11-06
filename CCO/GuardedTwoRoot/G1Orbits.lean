import CCO.GuardedTwoRoot.G1Actions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Range
import Lean.Elab.Tactic.Omega

/-! Infinitely many genuine real clones over every finite actual base.
Only the moved point's block/bit fibre is permuted; all owner blocks
stay literal. These are actual old motions, not supplied orbit providers. -/

namespace CCO.GuardedTwoRoot.G1
noncomputable section

def cloneSwap (x : Real) (n : ℕ) : Aut :=
  wreathAut (Equiv.refl ℕ) (fun _ => Equiv.refl Bool)
    (fun t => if t = (block x,bit x) then Equiv.swap (clone x) n else Equiv.refl ℕ)

theorem cloneSwap_self (x : Real) (n : ℕ) :
    cloneSwap x n • x = ((block x,bit x),n) := by
  apply real_ext (x := cloneSwap x n • x) (y := ((block x,bit x),n))
  · rfl
  · rfl
  · change (if (block x,bit x) = (block x,bit x) then
      Equiv.swap (clone x) n else Equiv.refl ℕ) (clone x) = n
    simp

theorem cloneSwap_block (x z : Real) (n : ℕ) : block (cloneSwap x n • z) = block z := rfl

theorem cloneSwap_fixed (x z : Real) (n : ℕ) (hz : z ≠ x) (hn : clone z ≠ n) :
    cloneSwap x n • z = z := by
  classical
  apply real_ext (x := cloneSwap x n • z) (y := z)
  · rfl
  · rfl
  · change (if (block z,bit z) = (block x,bit x) then
      Equiv.swap (clone x) n else Equiv.refl ℕ) (clone z) = clone z
    by_cases h : (block z,bit z) = (block x,bit x)
    · rw [if_pos h]
      have hzx : clone z ≠ clone x := by
        intro he
        exact hz (real_ext (congrArg Prod.fst h) (congrArg Prod.snd h) he)
      exact Equiv.swap_apply_of_ne_of_ne hzx hn
    · rw [if_neg h]
      rfl

/-- A countable family of distinct actual images, moved by old
automorphisms fixing EVERY point of the given finite old base. -/
theorem infinite_clone_family (D : Set Real) (hD : D.Finite)
    (x : Real) (hx : x ∉ D) :
    ∃ (image : ℕ → Real) (motion : ℕ → Aut), Function.Injective image ∧
      (∀ n, motion n • x = image n) ∧
      (∀ n z, z ∈ D → motion n • z = z) ∧
      (∀ n z, block (motion n • z) = block z) := by
  classical
  let Z := hD.toFinset
  let bound := Z.sup clone
  let target (n : ℕ) := bound + 1 + n
  let image (n : ℕ) : Real := ((block x,bit x),target n)
  let motion (n : ℕ) := cloneSwap x (target n)
  refine ⟨image,motion,?_,fun n => cloneSwap_self x (target n),?_,
    fun n z => cloneSwap_block x z (target n)⟩
  · intro n m h
    have hh := congrArg clone h
    change bound + 1 + n = bound + 1 + m at hh
    omega
  · intro n z hz
    apply cloneSwap_fixed
    · exact fun he => hx (he ▸ hz)
    · have hle : clone z ≤ bound := Finset.le_sup (hD.mem_toFinset.mpr hz)
      dsimp only [target]
      omega

end
end CCO.GuardedTwoRoot.G1
