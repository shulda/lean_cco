import CCO.UnarySupport.BoundaryLanguages

namespace CCO.UnarySupport.Boundaries
open Structure

def undefinedUnary : Structure (unarySignature Unit) Unit :=
  unary (fun _ _ => ∅) (by intro F x y z hy; exact False.elim hy)

def identityUnary (V : Type) : Structure (unarySignature Unit) V :=
  unary (fun _ x => {x}) (by intro F x y z hy hz; exact hy.trans hz.symm)

theorem identity_total (V : Type) : (identityUnary V).Total := by
  intro F x hx
  exact ⟨x, rfl⟩

def undefinedToIdentity : Hom undefinedUnary (identityUnary Unit) where
  point := id
  sort_eq _ := rfl
  map_func _ _ _ h := False.elim h
  map_rel R := Empty.elim R

theorem undefined_not_total : ¬ undefinedUnary.Total := by
  intro h
  obtain ⟨x, hx⟩ := h () () rfl
  exact hx

theorem undefined_not_domain_embedding : ¬ Nonempty (Embedding undefinedUnary (identityUnary Unit)) := by
  rintro ⟨e⟩
  obtain ⟨z, hz, _⟩ := e.reflect_func () () (e.point ()) rfl
  exact hz

/-- Same-carrier completion may add a previously undefined domain; a
domain-reflecting embedding cannot do this. -/
theorem mere_completion_counterexample :
    Nonempty (Hom undefinedUnary (identityUnary Unit)) ∧
    (identityUnary Unit).Total ∧ ¬ undefinedUnary.Total ∧
    ¬ Nonempty (Embedding undefinedUnary (identityUnary Unit)) :=
  ⟨⟨undefinedToIdentity⟩, identity_total Unit, undefined_not_total, undefined_not_domain_embedding⟩

def branching : Structure (unarySignature Bool) (Fin 3) :=
  unary (fun F x => if x = 0 then {if F then 2 else 1} else ∅)
    (by intro F x y z hy hz; split at hy <;> simp_all)

theorem branching_generated : branching.closureAt 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  fin_cases x
  · exact branching.mem_closureAt 0
  · exact ⟨0, rfl, Relation.ReflTransGen.refl.tail ⟨false, by simp [branching, unary]⟩⟩
  · exact ⟨0, rfl, Relation.ReflTransGen.refl.tail ⟨true, by simp [branching, unary]⟩⟩

def weakLeft : Set (Fin 3) := {x | x = 0 ∨ x = 1}
def weakRight : Set (Fin 3) := {x | x = 0 ∨ x = 2}

/-- Weak graph restrictions may delete values outside a chosen factor. -/
noncomputable def weakGraph (S : Set (Fin 3)) (F : Bool) (x : Fin 3) : Set (Fin 3) :=
  by classical exact if x ∈ S then branching.func F x ∩ S else ∅

theorem branching_weak_union :
    weakLeft ∪ weakRight = Set.univ ∧ weakLeft ≠ Set.univ ∧ weakRight ≠ Set.univ ∧
    (∀ F x, branching.func F x = weakGraph weakLeft F x ∪ weakGraph weakRight F x) ∧
    ¬ branching.IsClosed weakLeft ∧ ¬ branching.IsClosed weakRight := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; fin_cases x <;> simp [weakLeft, weakRight]
  · intro h
    have : (2 : Fin 3) ∈ weakLeft := h ▸ Set.mem_univ 2
    simp [weakLeft] at this
  · intro h
    have : (1 : Fin 3) ∈ weakRight := h ▸ Set.mem_univ 1
    simp [weakRight] at this
  · intro F x
    ext y
    cases F <;> fin_cases x <;> fin_cases y <;>
      simp [branching, unary, weakGraph, weakLeft, weakRight]
  · intro hc
    have h := hc true 0 (by simp [weakLeft]) (by simp [branching, unary] : (2 : Fin 3) ∈ branching.func true 0)
    simp [weakLeft] at h
  · intro hc
    have h := hc false 0 (by simp [weakRight]) (by simp [branching, unary] : (1 : Fin 3) ∈ branching.func false 0)
    simp [weakRight] at h

theorem domain_suppression_counterexample :
    branching.Irreducible ∧ branching.closureAt 0 = Set.univ ∧
    (∀ F x, branching.func F x = weakGraph weakLeft F x ∪ weakGraph weakRight F x) ∧
    ¬ branching.IsClosed weakLeft ∧ ¬ branching.IsClosed weakRight := by
  exact ⟨irreducible_of_generated branching 0 branching_generated, branching_generated,
    branching_weak_union.2.2.2.1, branching_weak_union.2.2.2.2.1, branching_weak_union.2.2.2.2.2⟩

theorem identity_closed (V : Type) (S : Set V) : (identityUnary V).IsClosed S := by
  intro F x hx y hy
  have he : y = x := hy
  exact he ▸ hx

def identitySplit : (identityUnary Bool).FreeDecomposition where
  left := {false}
  right := {true}
  left_closed := identity_closed _ _
  right_closed := identity_closed _ _
  cover := by ext x; cases x <;> simp
  left_proper h := by have h' : true ∈ ({false} : Set Bool) := h ▸ Set.mem_univ true; cases h'
  right_proper h := by have h' : false ∈ ({true} : Set Bool) := h ▸ Set.mem_univ false; cases h'
  rel_local R := Empty.elim R

theorem identity_irreducible_subsingleton (S : Set Bool) (hS : (identityUnary Bool).IsClosed S)
    (hirr : ((identityUnary Bool).induce S hS).Irreducible) : S.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hfull : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    cases x <;> cases y <;> cases z <;> simp_all
  let d : ((identityUnary Bool).induce S hS).FreeDecomposition := {
    left := {z | z.val = false}
    right := {z | z.val = true}
    left_closed := by
      intro F x hx y hy
      have he : y.val = x.val := hy
      exact he.trans hx
    right_closed := by
      intro F x hx y hy
      have he : y.val = x.val := hy
      exact he.trans hx
    cover := by ext z; cases hz : z.val <;> simp [hz]
    left_proper := by
      intro he
      have ht : true ∈ S := hfull ▸ Set.mem_univ true
      have hbad : (⟨true, ht⟩ : S) ∈ {z | z.val = false} := he ▸ Set.mem_univ _
      cases hbad
    right_proper := by
      intro he
      have hf : false ∈ S := hfull ▸ Set.mem_univ false
      have hbad : (⟨false, hf⟩ : S) ∈ {z | z.val = true} := he ▸ Set.mem_univ _
      cases hbad
    rel_local := fun R => Empty.elim R }
  exact hirr.false d

/-- The actual class of empty/singleton identity-unary diagrams. -/
def identitySmall {V : Type} (D : Structure (unarySignature Unit) V) : Prop :=
  (∀ x y : V, x = y) ∧ ∀ F x, D.func F x = {x}

theorem identity_irreducibles_actual :
    ∀ S (hS : (identityUnary Bool).IsClosed S),
      ((identityUnary Bool).induce S hS).Irreducible →
      identitySmall ((identityUnary Bool).induce S hS) := by
  intro S hS hirr
  refine ⟨?_, ?_⟩
  · intro x y
    exact Subtype.ext (identity_irreducible_subsingleton S hS hirr x.property y.property)
  · intro F x
    ext y
    change y.val = x.val ↔ y = x
    exact ⟨Subtype.ext, congrArg Subtype.val⟩

theorem identitySmall_total {V : Type} (D : Structure (unarySignature Unit) V)
    (hD : identitySmall D) : D.Total := by
  intro F x hx
  exact ⟨x, (hD.2 F x).symm ▸ Set.mem_singleton x⟩

theorem two_variable_counterexample :
    (∀ S (hS : (identityUnary Bool).IsClosed S),
      ((identityUnary Bool).induce S hS).Irreducible →
      identitySmall ((identityUnary Bool).induce S hS)) ∧
    (∀ (V : Type) (D : Structure (unarySignature Unit) V), identitySmall D → ∀ x y : V, x = y) ∧
    ¬ (∀ x y : Bool, x = y) := by
  exact ⟨identity_irreducibles_actual, fun _ _ h => h.1,
    fun h => Bool.false_ne_true (h false true)⟩

end CCO.UnarySupport.Boundaries
