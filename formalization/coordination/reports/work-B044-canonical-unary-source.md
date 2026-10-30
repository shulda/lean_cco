# B044 support — the actual canonical unary child source

Actual implementation author: `/root/b043_point_sap`.
Owned files: `CCO/APCharacter/SourceAge/UnarySource*.lean`.
This implements the source construction, whole-structure homogeneous action
and actual semantic CCO after the independently constructed old-reduct
identification. Root supplies the proved `SourceAge.old_reduct_equiv` from
actual finite extensions/back-and-forth, not an opaque isomorphism premise.
Source contracts, original source pin and accepted APIs remain unchanged.

## Stable internal identification and actual mark

`UnarySource.Identification S H completion` retains the literal equivalence
`Sigma X ≃ Age.Limit S H completion`, decoded old owner sort and decoded
old tagged optional pair colour. These three fields are definitionally the
output of root's proved `SourceAge.old_reduct_equiv`.

`mark I x` is the decoded unary bit of the SAME displayed point `I.equiv x`.
`finite_chart` factors every finite tuple, including repetitions, through
ONE actual finite chart of the limit chain and recovers its complete old
ordered colours and bits. `global_marking` transports that chart's actual
legal pair constraints to prove `M.GlobalMarking (mark I)`. No global
marking is supplied to the theorem as a premise.

`β I i = {ε : Bit // M.validBit i ε}` is the actual finite set of valid
children. `tag I i x` is the proved-valid mark of x. `inhabited I` proves
EVERY such child nonempty: an actual old singleton with that valid bit is
legal by the identity mask, embeds as an actual finite marked chart into
the SAME limit, and pulls back through the old-reduct identification.
There is no separate child-nonemptiness oracle. The proof includes inactive,
finite and empty ambient-source cases wherever their source types permit them.

`source I` is exactly the existing `Rank.source S (β I) (tag I) (inhabited I)`.
It retains the SAME original real carrier in each old sort, partitioned by
actual unary marks, with the exact occurring-subtype palettes. Original
sort/carrier/atom universes u/v/w stay fixed. Its child carriers inherit
countability from the corresponding original old carrier.

## Actual whole expanded group and homogeneity

`oldEquiv I` is the actual global bijection from all canonical child points
to `Sigma X`; its map forgets only the unary tag. `newEquiv I` composes it
with the proved old-reduct bijection, giving the actual equivalence from
ALL canonical child points to the marked Fraïssé limit.

`FullGroup I` is `ULift.{t}` of the FULL first-order automorphism group of
that entire limit. The actual group multiplication/inverse are whole
first-order composition/inverse; the group remains in the original Type t.
`move` transports each whole automorphism along `newEquiv`. `move_child`
proves that literal owner names preserve every named child sort.
`childAction` restricts that SAME whole action to each canonical child
carrier; `smul_image` proves its exact compatibility with the whole limit.
No independent per-child actions or arbitrary chosen subgroup are used.

`homogeneous I : HomogeneousSource (source I) (FullGroup I)` is fully proved.
`eraseColour` forgets child names but retains every original optional atom;
`erase_tagged` and `new_colour` prove the exact colour dictionary.
`action_colours` derives preservation by every actual whole automorphism.
For arbitrary finite complete new-source tuples, equality is recognized
from the true optional diagonal, owner names and every ordered colour are
retained, and `Age.tuple_homogeneous` produces ONE actual automorphism of
the ENTIRE marked structure. `smul_image` transports its action back to the
same displayed child tuple. Neither whole expanded homogeneity nor child
homogeneity is assumed as a principal provider.

## Genuine semantic CCO transfer

`UnarySourceCCO.oldDiagram` erases only the occurring-atom subtype from a
new-source diagram, preserving its formal vertices, sort tags, specified
edges and converse law. `old_legal` proves its literal mask constraints
using actual source witnesses of each occurring atom and the constructed
global marking.

`newCycle` lifts EVERY simple old-diagram cycle to the same actual new
cycle. `cycle_realizes` converts the given new-source cycle homomorphism
into a literal whole marked-limit cycle realization through `newEquiv`.
Repeated realized points, collisions of nonadjacent cycle vertices and
independent witnesses for different cycles are retained.

`Age.marked_cco` then produces ONE complete marked-limit network witness.
`pullRealization` pulls each displayed point through `newEquiv.symm`,
proves its exact child label using the literal owner code, and proves each
original specified atom on the same child carrier using the exact colour
dictionary. No unnamed replacement source or separate realization is used.

`semanticCCO I : SemanticCCO.{u,v,z,w} (source I)` follows in arbitrary
formal-vertex universes. The marked-age API is used on actual finite
ordinals; the accepted `semanticCCO_of_fin` transports the proven result to
ALL finite vertex types/universes. Empty diagrams and equality-inclusive
old colours are retained. No new marked CCO or completion provider is
assumed: `completion` is the already proved actual finite construction
that root instantiates at the current source.

## Actual compilation and isolation

Exact Lean4.34.1/Lake5 and unchanged receiving manifest.
- Actual mark/valid-child/source target passed1434jobs.
- Whole action and homogeneous-source target passed1436jobs.
- Final semantic CCO target passed1438jobs, final module2.3seconds.

No broad local project build, test suite, axiom audit, root import change or
GitHub mutation was performed by this helper. Root owns public source
assembly, actual phase/seed/rank instantiation, source report and integration.
Only the four owned UnarySource files and this report are submitted here;
the earlier B043 private untracked dependency copies were preserved and
never staged. Received B044 dependencies remain their original authors'
work. The internal Identification interface must be instantiated with the
actual proved old-reduct equivalence in the final source export; it is not
by itself claimed to close the final current-source batch.
