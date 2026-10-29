import CCO.ExactCRT.AbstractRelations
import CCO.FinitePackets.Geometry.RelativeIndices
import Mathlib.Order.Minimal

/-! A genuinely abstract finite commuting equivalence-lattice argument.
No source homogeneity, exactness, countability or normalization occurs in
the theorem: a greatest finite-class member with one least strict upper
member forces a unique minimal infinite member. -/
universe v
namespace CCO.AclOwners.Unary
open ParityHasse.Original
variable {M : Type v}

def FiniteClasses (E : Setoid M) : Prop := ∀ x : M, Finite {y // E x y}
def FiniteIndex (E F : Setoid M) : Prop := ∀ x : M, Finite (RelativeClass E F x)

def bottomClassEquiv (F : Setoid M) (x : M) :
    RelativeClass ⊥ F x ≃ {y // F x y} where
  toFun := Quotient.lift id (fun _ _ h => Subtype.ext h)
  invFun := Quotient.mk''
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv _ := rfl

theorem finiteClasses_iff (F : Setoid M) : FiniteClasses F ↔ FiniteIndex ⊥ F := by
  constructor
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv F x).symm
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv F x)

theorem finiteClasses_mono {E F : Setoid M} (hEF : E ≤ F)
    (hF : FiniteClasses F) : FiniteClasses E := by
  intro x
  letI := hF x
  exact Finite.of_injective (fun y : {y // E x y} => (⟨y.val,hEF y.property⟩ : {y // F x y}))
    (fun _ _ h => Subtype.ext (congrArg (fun z : {y // F x y} => z.val) h))

theorem finiteIndex_trans (E F K : Setoid M) (hEF : E ≤ F) (hFK : F ≤ K)
    (hE : FiniteIndex E F) (hF : FiniteIndex F K) : FiniteIndex E K := by
  classical
  intro x
  letI := hF x
  letI : Fintype (RelativeClass F K x) := Fintype.ofFinite _
  let f := relativeCoarsening E F K hEF x
  have hfib (q : RelativeClass F K x) : Finite {p : RelativeClass E K x // f p = q} := by
    refine Quotient.inductionOn q ?_
    intro y
    letI := hE y.val
    exact Finite.of_equiv _ (relativeFibreEquiv E F K hEF hFK x y)
  letI : ∀ q : RelativeClass F K x, Fintype {p : RelativeClass E K x // f p = q} :=
    fun q => by letI := hfib q; exact Fintype.ofFinite _
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv f)

theorem finiteClasses_of_index {E F : Setoid M} (hEF : E ≤ F)
    (hE : FiniteClasses E) (h : FiniteIndex E F) : FiniteClasses F :=
  (finiteClasses_iff F).mpr
    (finiteIndex_trans ⊥ E F bot_le hEF ((finiteClasses_iff E).mp hE) h)

theorem finiteIndex_upper {E F K : Setoid M} (hEF : E ≤ F)
    (h : FiniteIndex E K) : FiniteIndex F K := by
  intro x
  letI := h x
  exact finite_relative_right E F K hEF x

theorem finiteIndex_lower {E F K : Setoid M} (hFK : F ≤ K)
    (h : FiniteIndex E K) : FiniteIndex E F := by
  intro x
  letI := h x
  exact finite_relative_left E F K hFK x

theorem finiteIndex_restrict (E F K : Setoid M) (h : FiniteIndex F K) :
    FiniteIndex (E ⊓ F) (E ⊓ K) := by
  intro x
  letI := h x
  exact Finite.of_injective _ (FinitePackets.Geometry.restrictionClassMap_injective E F K x)

theorem finiteIndex_join_finite (E F : Setoid M) (h : ExactCRT.Abstract.Permutes E F)
    (hF : FiniteClasses F) : FiniteIndex E (E ⊔ F) := by
  have hrel : FiniteIndex (E ⊓ F) F :=
    finiteIndex_upper bot_le ((finiteClasses_iff F).mp hF)
  intro x
  letI := hrel x
  apply Finite.of_equiv _ (relativeClassTransposition E F ?_ x)
  intro a b
  have hj := ExactCRT.Abstract.join_eq_comp F E h.symm
  rw [sup_comm] at hj
  exact Iff.of_eq (congrFun (congrFun hj a) b)

variable (L : Sublattice (Setoid M))

def MinimalInfinite (U : L) : Prop :=
  ¬ FiniteClasses U.val ∧ ∀ V : L, V < U → FiniteClasses V.val

theorem minimal_eq_of_le {U V : L} (hU : MinimalInfinite L U)
    (hV : MinimalInfinite L V) (hle : U ≤ V) : U = V := by
  by_contra hn
  exact hU.1 (hV.2 U (lt_of_le_of_ne hle hn))

theorem minimal_inf_finite {U V : L} (hU : MinimalInfinite L U)
    (hV : MinimalInfinite L V) (hne : U ≠ V) : FiniteClasses (U ⊓ V).val := by
  apply hU.2
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hne (minimal_eq_of_le L hU hV (by rw [← he]; exact inf_le_right))

theorem least_upper_eq_join (commutes : ExactCRT.Abstract.Commutes L)
    (F D : L) (finiteF : FiniteClasses F.val)
    (greatest : ∀ V : L, FiniteClasses V.val → V ≤ F)
    (strict : F < D) (least : ∀ V : L, F < V → D ≤ V)
    (U : L) (hU : MinimalInfinite L U) : D = U ⊔ F := by
  have hnot : ¬ U ≤ F := fun h => hU.1 (finiteClasses_mono h finiteF)
  have hsup : F < U ⊔ F := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hnot (he ▸ (show U ≤ U ⊔ F from le_sup_left)))
  have hDsup : D ≤ U ⊔ F := least _ hsup
  have hrel : FiniteIndex U.val (U ⊔ F).val :=
    finiteIndex_join_finite U.val F.val (commutes U F) finiteF
  have hr := finiteIndex_restrict D.val U.val (U ⊔ F).val hrel
  change FiniteIndex (D ⊓ U).val (D ⊓ (U ⊔ F)).val at hr
  have hinf : (D ⊓ (U ⊔ F)).val = D.val := congrArg Subtype.val (inf_eq_left.mpr hDsup)
  rw [hinf] at hr
  have hDU : ¬ FiniteClasses (D ⊓ U).val := by
    intro hfin
    have hD := finiteClasses_of_index
      (show (D ⊓ U).val ≤ D.val from inf_le_left) hfin hr
    exact strict.not_ge (greatest D hD)
  have hUD : U ≤ D := by
    by_contra h
    apply hDU
    apply hU.2
    apply lt_of_le_of_ne inf_le_right
    intro he
    exact h (by rw [← he]; exact inf_le_left)
  exact le_antisymm hDsup (sup_le hUD strict.le)

/-- C19: the abstract uniqueness statement, without an extra source or
model-theoretic premise. -/
theorem unique_minimal_infinite [Finite L]
    (commutes : ExactCRT.Abstract.Commutes L)
    (F D : L) (finiteF : FiniteClasses F.val)
    (greatest : ∀ V : L, FiniteClasses V.val → V ≤ F)
    (strict : F < D) (least : ∀ V : L, F < V → D ≤ V) :
    ∃! U : L, MinimalInfinite L U := by
  have hD : ¬ FiniteClasses D.val := fun h => strict.not_ge (greatest D h)
  obtain ⟨U,hU,hmin⟩ := wellFounded_lt.has_min {V : L | ¬ FiniteClasses V.val} ⟨D,hD⟩
  have hUmin : MinimalInfinite L U := ⟨hU,by
    intro V hVU
    by_contra hV
    exact hmin V hV hVU⟩
  refine ⟨U,hUmin,?_⟩
  intro V hV
  by_contra hne
  have hUV := minimal_inf_finite L hUmin hV (Ne.symm hne)
  have hDU := least_upper_eq_join L commutes F D finiteF greatest strict least U hUmin
  have hDV := least_upper_eq_join L commutes F D finiteF greatest strict least V hV
  have hVU : V ≤ U ⊔ F := by rw [← hDU]; rw [hDV]; exact le_sup_left
  have hsmall : U ⊔ V ≤ U ⊔ F := sup_le le_sup_left hVU
  have hrel : FiniteIndex U.val (U ⊔ V).val := finiteIndex_lower hsmall
    (finiteIndex_join_finite U.val F.val (commutes U F) finiteF)
  have hmeet : FiniteIndex (U ⊓ V).val V.val := by
    intro x
    letI := hrel x
    exact Finite.of_equiv _ (relativeClassTransposition U.val V.val (by
      intro a b
      have hj := ExactCRT.Abstract.join_eq_comp V.val U.val (commutes V U)
      rw [sup_comm] at hj
      exact Iff.of_eq (congrFun (congrFun hj a) b)) x).symm
  exact hV.1 (finiteClasses_of_index (show (U ⊓ V).val ≤ V.val from inf_le_right) hUV hmeet)

end CCO.AclOwners.Unary
