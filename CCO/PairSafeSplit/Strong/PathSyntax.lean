import CCO.PairSafeSplit.Strong.Realization
import CCO.APCharacter.PathNormalForm

/-! Literal positive paths in the ACTUAL canonical child source, retaining
all intermediate child labels and original diversity atoms. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open APCharacter APCharacter.SourceAge.UnarySource
open RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
variable (I : Identification S H completion)

theorem atom_allowed {c d : Rank.Child (β I)} (a : (source I).Atom c d) :
    M.allowed (some a.val) c.2.val d.2.val := by
  obtain ⟨x,y,hxy⟩ := a.property
  have h := (global_marking I).2 (⟨c.1,x.val⟩ : Sigma X) ⟨d.1,y.val⟩
  have hx : mark I ⟨c.1,x.val⟩ = c.2.val := congrArg Subtype.val x.property
  have hy : mark I ⟨d.1,y.val⟩ = d.2.val := congrArg Subtype.val y.property
  rw [hxy,hx,hy] at h
  exact h

theorem endpoint_allowed {c d : Rank.Child (β I)}
    (x : Rank.Point (β I) (tag I) c) (y : Rank.Point (β I) (tag I) d) :
    M.allowed (S.colour x.val y.val) c.2.val d.2.val := by
  have h := (global_marking I).2 (⟨c.1,x.val⟩ : Sigma X) ⟨d.1,y.val⟩
  have hx : mark I ⟨c.1,x.val⟩ = c.2.val := congrArg Subtype.val x.property
  have hy : mark I ⟨d.1,y.val⟩ = d.2.val := congrArg Subtype.val y.property
  rw [hx,hy] at h
  exact h

def forgetWord {c d : Rank.Child (β I)} :
    PositiveWord (source I) c d → PositiveWord S c.1 d.1
  | .single a => .single a.val
  | .cons a p => .cons a.val (forgetWord p)

theorem forgetWord_append {b c d : Rank.Child (β I)}
    (p : PositiveWord (source I) b c) (q : PositiveWord (source I) c d) :
    forgetWord I (PositiveWord.append (source I) p q) =
      PositiveWord.append S (forgetWord I p) (forgetWord I q) := by
  induction p with
  | single a => rfl
  | cons a p ih => simp only [PositiveWord.append,forgetWord,ih]

private theorem positive_append_assoc {J : Type*} {Y : J → Type*} (T : AtomicSource J Y)
    {a b c d : J} (p : PositiveWord T a b) (q : PositiveWord T b c) (r : PositiveWord T c d) :
    PositiveWord.append T (PositiveWord.append T p q) r =
      PositiveWord.append T p (PositiveWord.append T q r) := by
  induction p with
  | single a => rfl
  | cons a p ih => simp only [PositiveWord.append,ih]

inductive LiftedPath : Rank.Child (β I) → Rank.Child (β I) → Type (max u (max v w)) where
  | edge {c d} (a : (source I).Atom c d) : LiftedPath c d
  | snoc {b c d} (p : LiftedPath b c) (a : (source I).Atom c d) : LiftedPath b d

namespace LiftedPath
variable {I}

def word {c d : Rank.Child (β I)} : LiftedPath I c d → PositiveWord (source I) c d
  | .edge a => .single a
  | .snoc p a => PositiveWord.append (source I) p.word (.single a)

def oldPrefix {c d : Rank.Child (β I)}
    (p : LiftedPath I c d) : M.Prefix (i := c.1) (j := d.1) c.2.val d.2.val := by
  induction p with
  | @edge d a => exact .edge a.val c.2.property d.2.property (atom_allowed I a)
  | @snoc c d p a ih => exact .snoc ih a.val d.2.property (atom_allowed I a)

def append {b c d : Rank.Child (β I)} (p : LiftedPath I b c) :
    LiftedPath I c d → LiftedPath I b d
  | .edge a => .snoc p a
  | .snoc q a => .snoc (append p q) a

theorem word_append {b c d : Rank.Child (β I)} (p : LiftedPath I b c) (q : LiftedPath I c d) :
    (p.append q).word = PositiveWord.append (source I) p.word q.word := by
  induction q with
  | edge a => rfl
  | snoc q a ih =>
    change PositiveWord.append (source I) (p.append q).word (.single a) =
      PositiveWord.append (source I) p.word (PositiveWord.append (source I) q.word (.single a))
    rw [ih,positive_append_assoc]

def ofWord {c d : Rank.Child (β I)} : PositiveWord (source I) c d → LiftedPath I c d
  | .single a => .edge a
  | .cons a p => append (.edge a) (ofWord p)

theorem word_ofWord {c d : Rank.Child (β I)} (p : PositiveWord (source I) c d) :
    (ofWord p).word = p := by
  induction p with
  | single a => rfl
  | cons a p ih =>
    change ((LiftedPath.edge a).append (ofWord p)).word = _
    rw [word_append,ih]
    rfl

/-- The old word is the same literal diversity-atom sequence. RAW identity
outputs are retained; this does not assert distinctness of endpoints. -/
theorem old_word_relation {c d : Rank.Child (β I)} (p : LiftedPath I c d) :
    RawWord.relation S p.oldPrefix.word = PositiveWord.represented S (forgetWord I p.word) := by
  induction p with
  | edge a =>
    simp only [oldPrefix,word,MaskData.Prefix.word,RawWord.relation,TRel.comp_ident,
      forgetWord,PositiveWord.represented]
  | snoc p a ih =>
    simp only [oldPrefix,word,MaskData.Prefix.word,RawWord.relation_append,
      RawWord.relation,TRel.comp_ident,forgetWord_append,PositiveWord.represented_append,
      forgetWord,PositiveWord.represented]
    change TRel.comp (RawWord.relation S p.oldPrefix.word) (S.atomRel a.val) =
      TRel.comp (PositiveWord.represented S (forgetWord I p.word)) (S.atomRel a.val)
    rw [ih]

end LiftedPath
end
end CCO.PairSafeSplit.Strong
