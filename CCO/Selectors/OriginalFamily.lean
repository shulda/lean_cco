import CCO.Selectors.GateImage

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

def originalFamily : Family S := {D | IsExact S D}
def atomicFamily : Family S := {D | ∃ a, D.2.2 = ({a} : S.Menu D.1 D.2.1)}

theorem originalFamily_current (C : ExactCalculus S) : CurrentFamily S (originalFamily S) where
  exact h := h
  singleton a := StrongExact.exact_singleton S a
  opposite h := C.opposite h
  downward _ hE _ := hE

theorem atomicFamily_subset {J : Family S} (hJ : CurrentFamily S J) : atomicFamily S ⊆ J := by
  rintro ⟨i,j,D⟩ ⟨a,hD⟩
  change S.Atom i j at a
  change D = {a} at hD
  rw [hD]
  exact hJ.singleton a

theorem atomicFamily_card_le {J : Family S} (hJ : CurrentFamily S J) :
    Nat.card (atomicFamily S) ≤ Nat.card J :=
  Set.ncard_le_ncard (atomicFamily_subset S hJ)

/-- The atomic lower bound is the actual sum of the named diversity palette sizes. -/
theorem atomicFamily_card :
    Nat.card (atomicFamily S) = S.finiteSort.elems.sum fun i =>
      S.finiteSort.elems.sum fun j => Nat.card (S.Atom i j) := by
  classical
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  let f : (Σ i, Σ j, S.Atom i j) → atomicFamily S :=
    fun a => ⟨⟨a.1,a.2.1,{a.2.2}⟩,⟨a.2.2,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      rcases a with ⟨i,j,a⟩
      rcases b with ⟨i',j',b⟩
      have hv := congrArg Subtype.val h
      have hi := congrArg Sigma.fst hv
      cases hi
      have hj := congrArg (fun D : TaggedMenu S => D.2.1) hv
      cases hj
      have hab : ({a} : S.Menu i j) = {b} := by
        simpa only [f,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hv
      have heq : a = b := Set.singleton_injective hab
      cases heq
      rfl
    · rintro ⟨⟨i,j,D⟩,a,hD⟩
      change S.Atom i j at a
      change D = {a} at hD
      subst D
      exact ⟨⟨i,j,a⟩,rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]
  rfl

/-- Count ORIGINAL exact menus with their actual ordered endpoint tags. -/
noncomputable def originalMenuCount : Nat := S.finiteSort.elems.sum fun i =>
  S.finiteSort.elems.sum fun j => Nat.card {D : S.Menu i j // StrongExact.Exact S D}

theorem originalFamily_card : Nat.card (originalFamily S) = originalMenuCount S := by
  classical
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  letI : ∀ i j, Fintype {D : S.Menu i j // StrongExact.Exact S D} :=
    fun i j => Fintype.ofFinite _
  let e : (Σ i, Σ j, {D : S.Menu i j // StrongExact.Exact S D}) ≃ originalFamily S :=
    { toFun := fun D => ⟨⟨D.1,D.2.1,D.2.2.val⟩,D.2.2.property⟩
      invFun := fun D => ⟨D.val.1,D.val.2.1,⟨D.val.2.2,D.property⟩⟩
      left_inv := by rintro ⟨i,j,D,hD⟩; rfl
      right_inv := by rintro ⟨⟨i,j,D⟩,hD⟩; rfl }
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma]
  unfold originalMenuCount
  simp only [Nat.card_eq_fintype_card]
  rfl

end CCO.Selectors
