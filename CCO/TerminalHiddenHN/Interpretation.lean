import CCO.TerminalHiddenHN.EquivariantFunctions
import CCO.UnaryFreshFrames.Quotient.Named

/-! The structural data of a finite binary equivariant unary
interpretation on the original real sorts. These are the literal A02
inputs to standalone cofinality and readout: no SAP, CCO, terminal-cover,
hidden amalgamation or Ramsey hypothesis is part of this interface.
The actual MI interpretation will separately instantiate these data.
-/

universe u v w r l k
namespace CCO.TerminalHiddenHN

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

structure RealInterpretation
    (U : CCO.UnaryFreshFrames.Language.{max u l})
    {V : Type k} (P : CCO.UnaryFreshFrames.Structure U V) where
  finiteSorts : Finite U.Sorts
  finiteFuncs : Finite U.Func
  finiteRels : Finite U.Rel
  binary : ∀ R, U.arity R = 2
  realSort : ι ↪ U.Sorts
  root : ∀ i, X i → P.Carrier (realSort i)
  root_bijective : ∀ i, Function.Bijective (root i)
  motion : G →* P.Aut
  root_equivariant : ∀ (g : G) i (x : X i),
    (motion g) • (root i x).val = (root i (g • x)).val
  /-- A primitive with real output is only the identity. This also
  allows harmless named identities; it excludes every real selector. -/
  primitive_real_identity : ∀ F i, U.output F = realSort i → ∀ x, P.func F x = x
  /-- Each hidden sort has one genuine onto real-source projection
  term. It is uniform on that sort and creates no point in a finite host. -/
  projection : ∀ s : U.Sorts, ∃ i,
    ∃ q : CCO.UnaryFreshFrames.Term U (realSort i) s,
      Function.Surjective (fun x => P.typedEval q (root i x))
  atom : ∀ {i j}, S.Atom i j → U.Rel
  atom_iff : ∀ {i j} (a : S.Atom i j) (x : X i) (y : X j),
    P.rel (atom a)
      (fun n => if n.val = 0 then (root i x).val else (root j y).val) ↔
      S.atomRel a x y

end CCO.TerminalHiddenHN
