import CCO.UnaryFreshFrames.Quotient.Named

/-! The forced-factor and infinite-index clauses follow from full-Aut
singleton acl=closure; neither clause is assumed by these implications.
The hereditary SAP criterion discharges that closure equality in the source. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

/-- Actual singleton closure membership supplies a LITERAL well-sorted term
of the required output sort, not an arbitrary definable factor. -/
theorem exists_named_term_of_closure {j k : L.Sorts} (b : H.Carrier j) {v : V}
    (hv : v ∈ H.closureAt b.val) (hsort : H.sort v = k) :
    ∃ s : Term L j k, H.eval s b.val = v := by
  rcases b with ⟨b, hb⟩
  subst j
  rcases hv with ⟨z, hz, l, s, hs⟩
  change z = b at hz
  subst z
  have hl : l = k := (H.eval_sort s rfl).symm.trans ((congrArg H.sort hs).trans hsort)
  subst l
  exact ⟨s, hs⟩

/-- Actual subgroup transitivity gives full-Aut transitivity on the SAME
named real sort; no equality of the two groups is assumed. -/
theorem full_sort_transitive (G : Subgroup H.Aut) {i : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i)) :
    Quotient.Transitive (G := H.Aut) (M := H.Carrier i) := by
  intro x y
  obtain ⟨g, hg⟩ := ht x y
  exact ⟨g.val, hg⟩

/-- C20/C42 bridge: BOTH actual stabilizer orbits equal the named fibre
image. Full automorphisms preserve all named maps, while subgroup transitivity
supplies every point of the fibre. -/
theorem named_full_orbit_eq_fibreValues (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k) (x : H.Carrier i) :
    MulAction.orbit (MulAction.stabilizer H.Aut (H.typedEval p x)) (H.termFunction t x) =
      Quotient.FibreValues (H.typedEval p) (H.termFunction t) (H.typedEval p x) :=
  Quotient.orbit_eq_fibreValues (H.full_sort_transitive G ht) _
    (H.typedEval_full_equivariant p) _ (H.termFunction_full_equivariant t) x

/-- C38: every FULL automorphism over the quotient point fixes a forced
value. No supplied factor term or subgroup=full-group identification. -/
theorem forced_value_mem_dcl {i j k : L.Sorts} (p : Term L i j) (t : Term L i k)
    (hk : Quotient.KernelLe (H.typedEval p) (H.termFunction t)) (x : H.Carrier i) :
    H.termFunction t x ∈ Dcl H.Aut {(H.typedEval p x).val} := by
  intro g
  apply Quotient.forced_value_fixed (H.typedEval p) (H.typedEval_full_equivariant p)
    (H.termFunction t) (H.termFunction_full_equivariant t) hk x g.val
  apply Subtype.ext
  exact g.property _ rfl

/-- C40: equality at ONE real point gives the literal global named factor. -/
theorem named_factor_of_one_value (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k) (s : Term L j k) (x : H.Carrier i)
    (he : H.termFunction t x = H.eval s (H.eval p x.val)) :
    ∀ y : H.Carrier i, H.termFunction t y = H.eval s (H.eval p y.val) := by
  have h := Quotient.factor_of_one_value ht (H.typedEval p) (H.typedEval_equivariant G p)
    (H.termFunction t) (H.termFunction_equivariant G t)
    (H.termFunction s) (H.termFunction_equivariant G s) x he
  exact congrFun h

/-- C39–C40: singleton full-Aut closure equality supplies both existence and
GLOBAL namedness of every forced factor. -/
theorem forcedNamedFactors_of_acl (G : Subgroup H.Aut) {i j : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i)) (p : Term L i j)
    (x₀ : H.Carrier i)
    (hacl : ∀ b : V, Acl H.Aut {b} = H.closureAt b) : H.ForcedNamedFactors p := by
  intro k t hk
  have hpoint : ∀ x : H.Carrier i, H.termFunction t x ∈ H.closureAt (H.typedEval p x).val := by
    intro x
    rw [← hacl]
    exact dcl_subset_acl H.Aut _ (H.forced_value_mem_dcl p t hk x)
  obtain ⟨s, hs⟩ := H.exists_named_term_of_closure (H.typedEval p x₀)
    (hpoint x₀) (H.termFunction_output t x₀)
  exact ⟨s, H.named_factor_of_one_value G ht p t s x₀ hs.symm⟩

/-- C42: finite actual fibre-image sets give FULL-Aut algebraicity. -/
theorem finite_fibre_value_mem_acl {i j k : L.Sorts} (p : Term L i j) (t : Term L i k)
    (x : H.Carrier i)
    (hfin : (Quotient.FibreValues (H.typedEval p) (H.termFunction t)
      (H.typedEval p x)).Finite) :
    H.termFunction t x ∈ Acl H.Aut {(H.typedEval p x).val} := by
  apply hfin.subset
  intro y hy
  obtain ⟨g, hg, hgy⟩ := (mem_orbitOver_iff H.Aut).mp hy
  refine ⟨g • x, ?_, ?_⟩
  · change H.typedEval p (g • x) = H.typedEval p x
    rw [H.typedEval_full_equivariant p g x]
    apply Subtype.ext
    exact hg _ rfl
  · change H.eval t (g • x.val) = y
    rw [← H.aut_eval]
    exact hgy

/-- C43: transitivity of the ACTUAL subgroup supplies an off-closure move.
The conclusion is about named closure; it never equates the two group orbits. -/
theorem nonforced_value_not_mem_closure (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k)
    (hn : ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction t)) (x : H.Carrier i) :
    H.termFunction t x ∉ H.closureAt (H.typedEval p x).val := by
  obtain ⟨g, hmove⟩ := Quotient.exists_stabilizer_moves ht (H.typedEval p)
    (H.typedEval_equivariant G p) (H.termFunction t) (H.termFunction_equivariant G t) hn x
  intro hcl
  apply hmove
  have hfix : ∀ z ∈ ({(H.typedEval p x).val} : Set V),
      g.val.val • z = z := by
    intro z hz
    change z = (H.typedEval p x).val at hz
    subst z
    exact congrArg Subtype.val g.property
  exact H.closure_fixed g.val.val hfix _ hcl

/-- C44: FULL-Aut closure equality excludes EVERY finite proper relative
index, without assuming the index clause or the forced-factor clause. -/
theorem infiniteUnforcedIndex_of_acl (G : Subgroup H.Aut) {i j : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (hsurj : Function.Surjective (H.typedEval p))
    (hacl : ∀ b : V, Acl H.Aut {b} = H.closureAt b) : H.InfiniteUnforcedIndex p := by
  intro k t hn b hfin
  obtain ⟨x, hx⟩ := hsurj b
  have halg : H.termFunction t x ∈ Acl H.Aut {b.val} := by
    rw [← hx]
    apply H.finite_fibre_value_mem_acl p t x
    rwa [hx]
  rw [hacl] at halg
  have hoff := H.nonforced_value_not_mem_closure G ht p t hn x
  rw [hx] at hoff
  exact hoff halg

/-- C47: a missing ACTUAL named factor gives a full-Aut definable
point outside named closure, without assuming SAP. -/
theorem missing_named_factor_off_closure (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k)
    (hk : Quotient.KernelLe (H.typedEval p) (H.termFunction t))
    (hmissing : ¬ ∃ s : Term L j k, ∀ y : H.Carrier i,
      H.termFunction t y = H.eval s (H.eval p y.val)) (x : H.Carrier i) :
    H.termFunction t x ∈ Dcl H.Aut {(H.typedEval p x).val} ∧
      H.termFunction t x ∉ H.closureAt (H.typedEval p x).val := by
  refine ⟨H.forced_value_mem_dcl p t hk x, ?_⟩
  intro hcl
  obtain ⟨s, hs⟩ := H.exists_named_term_of_closure (H.typedEval p x)
    hcl (H.termFunction_output t x)
  exact hmissing ⟨s, H.named_factor_of_one_value G ht p t s x hs.symm⟩

/-- C48: a finite proper actual index gives algebraicity for FULL Aut and
an off-closure motion for the actual subgroup, without any SAP premise. -/
theorem finite_proper_index_off_closure (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k)
    (hn : ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction t)) (x : H.Carrier i)
    (hfin : (Quotient.FibreValues (H.typedEval p) (H.termFunction t)
      (H.typedEval p x)).Finite) :
    H.termFunction t x ∈ Acl H.Aut {(H.typedEval p x).val} ∧
      H.termFunction t x ∉ H.closureAt (H.typedEval p x).val :=
  ⟨H.finite_fibre_value_mem_acl p t x hfin,
    H.nonforced_value_not_mem_closure G ht p t hn x⟩

end CCO.UnaryFreshFrames.Structure
