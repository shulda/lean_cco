import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.RawExact.PrivatePaths
import CCO.RawExact.ReducedDirectWords
import CCO.ExactCRT.ExactLattice

/-! Saturated closed owner walks in the actual original source.  This
part uses no reachability, infinitude, amalgamation or CCO assumption. -/

universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact

abbrev Relation (M : Type v) := M → M → Prop

/-- The ordinary represented product; the empty word is real equality. -/
def relationProduct {M : Type v} : List (Relation M) → Relation M
  | [] => Eq
  | R :: rs => RawSymmetric.compose R (relationProduct rs)

theorem relationProduct_append {M : Type v} (rs ts : List (Relation M)) :
    relationProduct (rs ++ ts) =
      RawSymmetric.compose (relationProduct rs) (relationProduct ts) := by
  induction rs with
  | nil =>
      funext x y
      apply propext
      constructor
      · intro h; exact ⟨x,rfl,h⟩
      · rintro ⟨z,rfl,h⟩; exact h
  | cons R rs ih =>
      change RawSymmetric.compose R (relationProduct (rs ++ ts)) = _
      rw [ih]
      exact (raw_comp_assoc R (relationProduct rs) (relationProduct ts)).symm

def ownerSaturate {M : Type v} (E : Setoid M) (R : Relation M) : Relation M :=
  RawSymmetric.compose (RawSymmetric.compose E R) E

theorem owner_comp_self {M : Type v} (E : Setoid M) :
    RawSymmetric.compose E E = E.r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩; exact E.trans hxz hzy
  · intro hxy; exact ⟨y,hxy,E.refl y⟩

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
include H

theorem relationProduct_invariant (rs : List (Relation M))
    (h : ∀ R ∈ rs, ColourInvariant S () R) :
    ColourInvariant S () (relationProduct rs) := by
  induction rs with
  | nil =>
      intro x y x' y' hc
      simpa only [relationProduct, Sigma.mk.injEq, heq_eq_eq, true_and] using
        (S.colour_none_iff x y).symm.trans
          ((congrArg (fun c => c = none) hc).to_iff.trans (S.colour_none_iff x' y'))
  | cons R rs ih =>
      exact colourInvariant_comp S H (h R (by simp))
        (ih (fun T hT => h T (by simp [hT])))

/-- One occurrence of E makes the whole invariant product E-saturated. -/
theorem owner_absorbs_product (E : ColourEq S ()) (rs : List (Relation M))
    (hInv : ∀ R ∈ rs, ColourInvariant S () R) (hE : E.val.r ∈ rs) :
    RawSymmetric.compose E (relationProduct rs) = relationProduct rs := by
  induction rs with
  | nil => simp at hE
  | cons R rs ih =>
      rcases List.mem_cons.mp hE with hR | hTail
      · subst R
        change RawSymmetric.compose E
          (RawSymmetric.compose E (relationProduct rs)) = _
        rw [← raw_comp_assoc, owner_comp_self]
        rfl
      · change RawSymmetric.compose E
          (RawSymmetric.compose R (relationProduct rs)) = _
        rw [← raw_comp_assoc,
          invariant_relations_commute S H E.property (hInv R (by simp)),
          raw_comp_assoc,
          ih (fun T hT => hInv T (by simp [hT])) hTail]
        rfl

theorem owner_saturate_product (E : ColourEq S ()) (rs : List (Relation M))
    (hInv : ∀ R ∈ rs, ColourInvariant S () R) (hE : E.val.r ∈ rs) :
    ownerSaturate E.val (relationProduct rs) = relationProduct rs := by
  unfold ownerSaturate
  rw [owner_absorbs_product S H E rs hInv hE,
    invariant_relations_commute S H (relationProduct_invariant S H rs hInv) E.property,
    owner_absorbs_product S H E rs hInv hE]

/-- Keeping a terminal E rather than an equality makes the statement
include empty walks without inventing an atomic edge. -/
def saturatedProduct {M : Type v} (E : Setoid M) : List (Relation M) → Relation M
  | [] => E
  | R :: rs => RawSymmetric.compose (ownerSaturate E R) (saturatedProduct E rs)

theorem saturatedProduct_eq (E : ColourEq S ()) (rs : List (Relation M))
    (hInv : ∀ R ∈ rs, ColourInvariant S () R) :
    saturatedProduct E.val rs = ownerSaturate E.val (relationProduct rs) := by
  induction rs with
  | nil =>
      funext x y
      apply propext
      constructor
      · intro h; exact ⟨y,⟨y,h,rfl⟩,E.val.refl y⟩
      · rintro ⟨z,⟨u,hxu,rfl⟩,hzy⟩; exact E.val.trans hxu hzy
  | cons R rs ih =>
      rw [saturatedProduct, ih (fun T hT => hInv T (by simp [hT]))]
      unfold ownerSaturate
      have hEE := owner_comp_self E.val
      have hc := invariant_relations_commute S H (hInv R (by simp)) E.property
      have ht := invariant_relations_commute S H
        (relationProduct_invariant S H rs (fun T hT => hInv T (by simp [hT]))) E.property
      simp only [raw_comp_assoc, relationProduct]
      rw [← raw_comp_assoc E.val.r E.val.r, hEE]
      rw [← raw_comp_assoc R E.val.r, hc, raw_comp_assoc]
      rw [← raw_comp_assoc E.val.r E.val.r, hEE]

/-- C02. A genuine saturated owner loop, with at least one E factor,
produces the entire real diagonal in the unsaturated represented word. -/
theorem closed_owner_walk (E : ColourEq S ()) (rs : List (Relation M))
    (hInv : ∀ R ∈ rs, ColourInvariant S () R) (hE : E.val.r ∈ rs)
    (x : M) (hLoop : saturatedProduct E.val rs x x) :
    ∀ y : M, relationProduct rs y y := by
  have hx : relationProduct rs x x := by
    rwa [saturatedProduct_eq S H E rs hInv,
      owner_saturate_product S H E rs hInv hE] at hLoop
  intro y
  exact (relationProduct_invariant S H rs hInv x x y y
    ((S.colour_none_iff x x).mpr rfl |>.trans
      ((S.colour_none_iff y y).mpr rfl).symm)).mp hx

/-- Concatenate the actual blocks used to replace owner factors. -/
def flattenWords (ws : List (RawWord S () ())) : RawWord S () () :=
  ws.foldr (RawWord.append S) (.nil ())

omit H in
theorem flattenWords_relation (ws : List (RawWord S () ())) :
    RawWord.relation S (flattenWords S ws) =
      relationProduct (ws.map (RawWord.relation S)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change RawWord.relation S (RawWord.append S w (flattenWords S ws)) = _
      rw [RawWord.relation_append, ih]
      rfl

/-- C03: expansion is an actual closed RAW walk with all intermediate
points, rather than an assertion about independently chosen representatives. -/
theorem expanded_closed_owner_walk (E : ColourEq S ())
    (ws : List (RawWord S () ()))
    (hInv : ∀ R ∈ ws.map (RawWord.relation S), ColourInvariant S () R)
    (hE : E.val.r ∈ ws.map (RawWord.relation S))
    (x : M) (hLoop : saturatedProduct E.val (ws.map (RawWord.relation S)) x x)
    (y : M) : Nonempty (WordPath S (flattenWords S ws) y y) := by
  apply (wordPath_iff_relation S _ _ _).mpr
  rw [flattenWords_relation]
  exact closed_owner_walk S H E _ hInv hE x hLoop y

omit H in
/-- Reachability supplies exactness; it is not a second provider input. -/
theorem exact_of_represented_word (E : ColourEq S ()) (word : RawWord S () ())
    (hword : RawWord.relation S word = E.val.r) : ExactCRT.IsExactEq S (i := ()) E.val := by
  obtain ⟨x⟩ := S.nonemptySort ()
  refine ⟨⟨[word],x,x,?_⟩,?_⟩
  · intro w hw
    have hw' : w = word := by simpa using hw
    subst w
    simpa only [hword] using E.val.refl x
  · funext x y
    apply propext
    simp only [evaluate, List.mem_singleton, forall_eq]
    exact congrFun (congrFun hword x) y |>.to_iff

omit H in
/-- Reflexivity excludes a single diversity edge; nonidentity excludes
zero. Thus private reachable-owner paths have a genuine fresh interior. -/
theorem represented_nonidentity_length (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r) :
    2 ≤ diversityLength S word := by
  by_contra hn
  have hle : diversityLength S word ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | ho
  · have heq := eq_of_heq (erase_zero_length_heq_nil S word hz)
    apply hne
    apply Subtype.ext
    apply Setoid.ext
    intro x y
    have hr := RawWord.relation_eraseEquality S word
    rw [heq] at hr
    exact (congrFun (congrFun (hword.symm.trans hr.symm) x) y).to_iff
  · obtain ⟨a,ha⟩ := one_length_word_is_atom S word ho
    obtain ⟨x⟩ := S.nonemptySort ()
    have hh : S.atomRel a x x := by simpa only [← ha,hword] using E.val.refl x
    exact S.atomRel_ne hh rfl

end CCO.OwnerTransversal
