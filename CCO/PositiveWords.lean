import CCO.RawWords
import CCO.RawStrongBridge
import CCO.SAPPoint
import CCO.SAPEdge

/-!
# Genuinely positive typed diversity words

A positive word has at least one diversity atom. It cannot contain an
artificial identity letter, and its strongly typed profile uses the
three-distinct-point product, not RAW composition. Its represented
predicate is equality-inclusive and can have real diagonal outputs.

The word append laws are proved for arbitrary repeated named sorts.
This module supplies the algebraic half of the B001 positive-word bridge.
-/

universe u v w

namespace CCO

inductive PositiveWord {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) :
    ι → ι → Type (max u (max v w)) where
  | single {i j : ι} (a : S.Atom i j) : PositiveWord S i j
  | cons {i j k : ι} (a : S.Atom i j)
      (rest : PositiveWord S j k) : PositiveWord S i k

namespace PositiveWord

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {i j k : ι}

/-- Actual RAW relation of a nonempty, purely diversity word. -/
def represented {i j : ι} : PositiveWord S i j → TRel X i j
  | .single a => S.atomRel a
  | .cons a rest => TRel.comp (S.atomRel a) (represented rest)

/-- Iterated STRONG diversity product, without adjoined equality. -/
def profile {i j : ι} : PositiveWord S i j → S.Menu i j
  | .single a => {a}
  | .cons a rest => S.product {a} (profile rest)

/-- Genuinely composable concatenation with no empty word. -/
def append {i j k : ι} :
    PositiveWord S i j → PositiveWord S j k → PositiveWord S i k
  | .single a, rest => .cons a rest
  | .cons a tail, rest => .cons a (append tail rest)

/-- Lossless conversion to the RAW-word language with genuine loop
identity units, despite the positive word containing no identity letters. -/
def toRawWord {i j : ι} :
    PositiveWord S i j → RawWord S i j
  | .single a => .atom a (.nil _)
  | .cons a rest => .atom a (toRawWord rest)

theorem represented_toRawWord (w : PositiveWord S i j) :
    represented S w = RawWord.relation S (toRawWord S w) := by
  induction w with
  | single a =>
      change S.atomRel a =
        TRel.comp (S.atomRel a) (TRel.ident X _)
      exact (TRel.comp_ident (S.atomRel a)).symm
  | cons a rest ih =>
      change TRel.comp (S.atomRel a) (represented S rest) =
        TRel.comp (S.atomRel a)
          (RawWord.relation S (toRawWord S rest))
      rw [ih]

theorem represented_append (w : PositiveWord S i j)
    (v : PositiveWord S j k) :
    represented S (append S w v) =
      TRel.comp (represented S w) (represented S v) := by
  induction w with
  | single a => rfl
  | cons a rest ih =>
      change TRel.comp (S.atomRel a)
          (represented S (append S rest v)) =
        TRel.comp (TRel.comp (S.atomRel a) (represented S rest))
          (represented S v)
      rw [ih v, TRel.comp_assoc]

theorem profile_append (hEdge : S.RealEdgeGluing)
    (w : PositiveWord S i j) (v : PositiveWord S j k) :
    profile S (append S w v) =
      S.product (profile S w) (profile S v) := by
  induction w with
  | single a => rfl
  | cons a rest ih =>
      change S.product {a} (profile S (append S rest v)) =
        S.product (S.product {a} (profile S rest)) (profile S v)
      rw [ih v, S.product_assoc_of_edge_gluing hEdge]

theorem profile_append_of_SAP
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) (v : PositiveWord S j k) :
    profile S (append S w v) =
      S.product (profile S w) (profile S v) :=
  profile_append S (S.realEdgeGluing_of_SAP H sap) w v

theorem profile_nonempty (hPoint : S.RealPointGluing)
    (w : PositiveWord S i j) : (profile S w).Nonempty := by
  induction w with
  | single a => exact ⟨a, rfl⟩
  | cons a rest ih =>
      exact S.product_nonempty_of_point_gluing hPoint
        ⟨a, rfl⟩ ih

theorem profile_nonempty_of_SAP
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) : (profile S w).Nonempty :=
  profile_nonempty S (S.realPointGluing_of_SAP H sap) w

/-- A one-letter positive word contains exactly its one true diversity
atom in the represented diversity guard. -/
theorem single_guard (a : S.Atom i j) :
    S.diversityGuard (represented S (.single a)) =
      ({a} : S.Menu i j) := by
  change S.diversityGuard (S.atomRel a) = ({a} : S.Menu i j)
  rw [S.atomRel_as_menu, S.diversityGuard_menuRel]

/-- At length two, guarded RAW composition equals the actual STRONG
triangle product without any SAP assumption. For longer words the
additional finite-diagram injectivization theorem is required. -/
theorem two_letter_guard (a : S.Atom i j) (b : S.Atom j k) :
    S.diversityGuard (represented S (.cons a (.single b))) =
      profile S (.cons a (.single b)) := by
  change S.diversityGuard (TRel.comp (S.atomRel a) (S.atomRel b)) =
    S.product ({a} : S.Menu i j) ({b} : S.Menu j k)
  rw [S.atomRel_as_menu a, S.atomRel_as_menu b]
  exact (S.product_eq_raw_two_step_guard
    ({a} : S.Menu i j) ({b} : S.Menu j k)).symm


/-!
## Full positive-word guard under actual SAP

The induction needs a slightly stronger invariant than the endpoint guard
alone: any represented *closed* positive word absorbs an incoming diversity
menu on the right. A closed real walk may repeat vertices; the supported-fork
lemma makes precisely that diagonal contribution redundant in the STRONG
profile. This avoids encoding diagonal walk outputs as fake STRONG atoms.
-/

/-- Represented positive words are invariant under the original
colour-preserving group action; no SAP assumption is needed here. -/
theorem represented_invariant_of_homogeneous
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (w : PositiveWord S i j) :
    TRel.Invariant (G := G) (represented S w) := by
  induction w with
  | single a =>
      intro g x y hxy
      change S.colour (g • x) (g • y) = some a
      exact (S.colourInvariant_of_homogeneous H g x y).trans hxy
  | cons a rest ih =>
      intro g x z hr
      change ∃ y, S.atomRel a x y ∧ represented S rest y z at hr
      obtain ⟨y, hxy, hyz⟩ := hr
      refine ⟨g • y, ?_, ih g y z hyz⟩
      exact (S.colourInvariant_of_homogeneous H g x y).trans hxy

/-- A right supported fork follows from a genuine point-glued triangle
and edge-glued associativity, including when sort labels repeat. -/
private theorem right_supported_fork
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    {i j k : ι} (a : S.Atom i j) (A : S.Menu k i) :
    A ⊆ S.product A
      (S.product ({a} : S.Menu i j) ({S.conv a} : S.Menu j i)) := by
  intro c hc
  obtain ⟨b, htri⟩ := hPoint c a
  have hMem : c ∈
      S.product (S.product A ({a} : S.Menu i j))
        ({S.conv a} : S.Menu j i) :=
    ⟨b, ⟨c, hc, a, by simp, htri⟩,
      S.conv a, by simp, S.triangle_rotate htri⟩
  rw [S.product_assoc_of_edge_gluing hEdge A
    ({a} : S.Menu i j) ({S.conv a} : S.Menu j i)] at hMem
  exact hMem

/-- A simultaneous induction: (1) the full diversity guard of a
represented positive word is its actual STRONG profile; (2) every
represented diagonal loop is absorbed on the right of ANY incoming
diversity menu. The second assertion supplies exactly the possible
middle-equals-last collision in the inductive step of (1). -/
private theorem guard_and_diagonal_absorption_of_SAP
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (w : PositiveWord S i j) :
    (S.diversityGuard (represented S w) = profile S w) ∧
    (∀ (e : j = i) (x : X i),
      represented S w x (e.symm ▸ x) →
      ∀ {k : ι} (A : S.Menu k i),
        A ⊆ S.product A (e ▸ profile S w)) := by
  have hPoint := S.realPointGluing_of_SAP H sap
  have hEdge := S.realEdgeGluing_of_SAP H sap
  induction w with
  | single a =>
      constructor
      · exact single_guard S a
      · intro e x hxx k A
        cases e
        change S.atomRel a x x at hxx
        exact False.elim ((S.atomRel_ne hxx) rfl)
  | cons a rest ih =>
      constructor
      · apply Set.Subset.antisymm
        · intro c hc
          rcases hc with ⟨x, z, hr, hxz⟩
          change ∃ y, S.atomRel a x y ∧ represented S rest y z at hr
          obtain ⟨y, hxy, hyz⟩ := hr
          cases hyzColour : S.colour y z with
          | some b =>
              have hb : b ∈ profile S rest := by
                rw [← ih.1]
                exact ⟨y, z, hyz, hyzColour⟩
              exact ⟨a, by simp, b, hb, ⟨x, y, z, hxy, hyzColour, hxz⟩⟩
          | none =>
              have hEq : (⟨_, y⟩ : Sigma X) = ⟨_, z⟩ :=
                (S.colour_none_iff y z).mp hyzColour
              have hSort := congrArg Sigma.fst hEq
              cases hSort
              have hPt : y = z := by
                simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hEq
              subst y
              have hAbs := ih.2 rfl z hyz
                ({a} : S.Menu _ _)
              have hca : c = a :=
                Option.some.inj (hxz.symm.trans hxy)
              subst c
              exact hAbs (by simp)
        · intro c hc
          rcases hc with ⟨a', ha', b, hb, ⟨x, y, z, hxy, hyz, hxz⟩⟩
          have haEq : a' = a := Set.mem_singleton_iff.mp ha'
          subst a'
          have hbGuard : b ∈
              S.diversityGuard (represented S rest) := by
            rw [ih.1]
            exact hb
          obtain ⟨y', z', hRest, hy'z'⟩ := hbGuard
          obtain ⟨g, hgy, hgz⟩ :=
            (S.pair_homogeneous_of_homogeneous H)
              y' y z' z (hy'z'.trans hyz.symm)
          have hTransport :=
            (represented_invariant_of_homogeneous S H rest) g y' z' hRest
          rw [hgy, hgz] at hTransport
          exact ⟨x, z, ⟨y, hxy, hTransport⟩, hxz⟩
      · intro e x hxx k A
        cases e
        change ∃ y, S.atomRel a x y ∧ represented S rest y x at hxx
        obtain ⟨y, hxy, hyx⟩ := hxx
        have hConverse : S.conv a ∈ profile S rest := by
          rw [← ih.1]
          exact ⟨y, x, hyx, (S.colour_swap x y a).mp hxy⟩
        have hSingleton :
            ({S.conv a} : S.Menu _ _) ⊆ profile S rest := by
          intro b hb
          have hEq : b = S.conv a := Set.mem_singleton_iff.mp hb
          simpa only [hEq] using hConverse
        exact (right_supported_fork S hPoint hEdge a A).trans
          (S.product_mono
            (fun _ h => h)
            (S.product_mono (fun _ h => h) hSingleton))

/-- STRONG C05 (word consequence): for every nonempty word made solely
from genuine diversity colours, the actual represented RAW endpoint
relation has exactly the iterated STRONG profile after removing its
REAL-diagonal outputs. The hypotheses are original finite homogeneity
and genuine age-SAP, not CCO/NR2 or a hidden collision-removal axiom. -/
theorem diversityGuard_represented_eq_profile_of_SAP
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) :
    S.diversityGuard (represented S w) = profile S w :=
  (guard_and_diagonal_absorption_of_SAP S H sap w).1

/-- The strong profile of a positive word also describes the diversity
guard of its equality-inclusive RAW-word encoding. -/
theorem diversityGuard_rawWord_eq_profile_of_SAP
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) :
    S.diversityGuard (RawWord.relation S (toRawWord S w)) =
      profile S w := by
  rw [← represented_toRawWord S w]
  exact diversityGuard_represented_eq_profile_of_SAP S H sap w

end PositiveWord
end CCO
