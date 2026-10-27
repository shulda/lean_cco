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
      rw [ih, TRel.comp_assoc]

theorem profile_append (hEdge : S.RealEdgeGluing)
    (w : PositiveWord S i j) (v : PositiveWord S j k) :
    profile S (append S w v) =
      S.product (profile S w) (profile S v) := by
  induction w with
  | single a => rfl
  | cons a rest ih =>
      change S.product {a} (profile S (append S rest v)) =
        S.product (S.product {a} (profile S rest)) (profile S v)
      rw [ih, S.product_assoc_of_edge_gluing hEdge]

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

end PositiveWord
end CCO
