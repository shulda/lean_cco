import CCO.TerminalPowers.GraphSource
import CCO.PositiveWords

/-! A positive exponent is part of the API. The private successor counter
is exponent minus one; its zero index denotes ONE atom, never equality. -/
universe u v w t
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) {i : ι}

private def positiveStage (t : S.Atom i i) : Nat → S.Menu i i
  | 0 => {t}
  | n+1 => S.product (positiveStage t n) {t}

def purePower (t : S.Atom i i) (n : ℕ+) : S.Menu i i :=
  positiveStage S t (n.val-1)

@[simp] theorem purePower_one (t : S.Atom i i) : purePower S t 1 = {t} := rfl

theorem purePower_succ (t : S.Atom i i) (n : ℕ+) :
    purePower S t ⟨n.val+1,Nat.succ_pos _⟩ = S.product (purePower S t n) {t} := by
  unfold purePower
  change positiveStage S t ((n.val+1)-1) = S.product (positiveStage S t (n.val-1)) {t}
  have hpos : 0 < n.val := n.property
  have he : (n.val+1)-1 = (n.val-1)+1 := by omega
  rw [he]
  rfl

def repeatedWord (t : S.Atom i i) : Nat → PositiveWord S i i
  | 0 => .single t
  | n+1 => .cons t (repeatedWord t n)

theorem repeatedWord_represented (t : S.Atom i i) (n : Nat) :
    PositiveWord.represented S (repeatedWord S t n) = relPow (S.atomRel t) (n+1) := by
  induction n with
  | zero =>
    funext x y
    exact propext (relPow_one _ x y).symm
  | succ n ih =>
    change TRel.comp (S.atomRel t) (PositiveWord.represented S (repeatedWord S t n)) = _
    rw [ih]
    rfl

theorem repeatedWord_profile (t : S.Atom i i) (n : Nat) :
    PositiveWord.profile S (repeatedWord S t n) = purePower S t ⟨n+1,Nat.succ_pos _⟩ := by
  change PositiveWord.profile S (repeatedWord S t n) = positiveStage S t n
  induction n with
  | zero => rfl
  | succ n ih =>
    change S.product {t} (PositiveWord.profile S (repeatedWord S t n)) = _
    rw [ih]
    exact S.loop_product_commute _ _

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)] (H : HomogeneousSource S G)

/-- C18: direct positive legal-triangle recursion, independent of SAP/NR2. -/
private theorem positiveStage_subset_connectivity (t : S.Atom i i) (n : Nat) :
    positiveStage S t n ⊆ connectivityPalette S H t := by
  induction n with
  | zero =>
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ atom_mem_connectivityPalette S H t
  | succ n ih =>
    rintro c ⟨a,ha,b,hb,x,y,z,hxy,hyz,hxz⟩
    have hb' : b = t := hb
    subst b
    have hxzC : Connected S H t x z :=
      (Connected S H t).val.trans (ih ha x y hxy) ⟨1,(relPow_one _ _ _).mpr hyz⟩
    intro x' z' hx'z'
    exact ((Connected S H t).property x z x' z' (hxz.trans hx'z'.symm)).mp hxzC

theorem purePower_subset_connectivity (t : S.Atom i i) (n : ℕ+) :
    purePower S t n ⊆ connectivityPalette S H t := positiveStage_subset_connectivity S H t _

include H in
/-- Selected B001 positive guarded-profile semantics, with no CCO premise. -/
theorem purePower_eq_guarded (sap : AgeSAP S) (t : S.Atom i i) (n : ℕ+) :
    purePower S t n = S.diversityGuard (relPow (S.atomRel t) n.val) := by
  have he := PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap
    (repeatedWord S t (n.val-1))
  rw [repeatedWord_represented,repeatedWord_profile] at he
  have hpos : 0 < n.val := n.property
  have hn : n.val-1+1 = n.val := by omega
  have hpn : (⟨n.val-1+1,Nat.succ_pos _⟩ : ℕ+) = n := by
    apply Subtype.ext
    exact hn
  rw [hpn,hn] at he
  exact he.symm

end CCO.TerminalPowers
