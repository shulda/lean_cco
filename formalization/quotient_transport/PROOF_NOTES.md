# B040 — invariant quotient transport and canonical return

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 50 claims and eight tasks prepare FOUR Foundations I
results and TWO auxiliary equations from
`sections/typed_invariant_quotient_transport.tex`. There are no theorem
imports or external providers: all arguments here are elementary action,
quotient, relation and lattice proofs, expanded in this package.

The point-lifting and orbital-pullback results already belong to the
SHARED B001 implementation/API requirements. B040 documents their full
proofs and improves preparation coverage; it does not allocate duplicate
receiving exports, change B001's additional exports or rewire existing
consumer imports. The two transport/return results are separate local
preparation. This is human proof preparation, not compiled Lean.

## N01: A canonical quotient label from actual predecessors

**D01/D03/D04; C01–C05.** All compositions are left-to-right existential
composition of ACTUAL typed binary relations, including equality
witnesses. Converse reverses coordinates. Universal relation `1_a`
differs from logical identity `Id_a`; no strong-diversity product is used.

A nonempty invariant relation between transitive nonempty endpoints is
serial and co-serial. Move either coordinate of one fixed witness by a
group element and use invariance. Finite composable products inherit
these properties. The group actions need not be faithful.

If `R;Rᵗ⊆E`, any two R-predecessors of a target y are E-equivalent.
Define `λ(y)=[x]_E` using ANY predecessor. Co-seriality supplies x;
the kernel containment makes the value independent of choices. The map
is equivariant. Seriality makes it onto a/E: for each x choose a target
of x and its label is [x]_E.

Equality of two target labels means exactly that their predecessors can
be joined by E. Hence

\[
 E^R=R^{\smile};E;R=\ker\lambda.
\]

This is an ACTUAL invariant equivalence. The induced equivariant
bijection `b/E^R→a/E` is denoted bar-λ; its inverse is the transport
`q_(R,E):a/E→b/E^R`. For every actual edge xRy it sends [x]_E to
[y]_(E^R), fixing its orientation without an unrelated quotient chart.

The kernel implication is a LOCAL conditional lemma. A02 supplies its
antecedent in the first source export. In the return proof C16 and C20
DERIVE that antecedent separately for each prefix and factor. The return
branch does not assume the first lemma's unrelated R-kernel premise.

## N02: Transport the whole invariant lattice interval and compose actual maps

**D02/D05/D06; C06–C12.** Equivalences H≥E correspond exactly to
equivalences H/E on a/E. Independence of representatives follows from
E⊆H, and inverse pullback is immediate. Equivariance preserves invariance
in both directions. Conjugate H/E by the actual quotient bijection from
N01 and pull it back to b. The resulting relation is literally

\[
 H^R=R^{\smile};H;R.
\]

This produces ALL invariant equivalences above E^R. The inverse sends
L≥E^R to `R;L;Rᵗ`. One can check the inverse by labels, or note that
`Id⊆R;Rᵗ⊆E⊆H`, so
`R;Rᵗ;H;R;Rᵗ=H`; the analogous target identity follows in the same way.
No exactness, commutation or distributive-lattice assertion is used.

An order isomorphism preserves bottom/top, all existing meets and joins,
covers and proper binary meet-irreducibility. The latter statement also
holds in the FULL invariant-equivalence lattices: if H≥E and H is a
meet of two equivalences, both factors lie above H and hence above E.
Thus the upper-interval and global meet-irreducibility tests agree at H.
The universal top is not counted as proper meet-irreducible.

For actual composable R:a→b, S:b→c, put the LITERAL `F=E^R` and
assume `S;Sᵗ⊆F`. Then

\[
 (R;S);(R;S)^{\smile}
 \subseteq R;F;R^{\smile}
 =R;R^{\smile};E;R;R^{\smile}\subseteq E.
\]

Both kernel hypotheses therefore give the composite kernel condition.
Associativity gives `E^(R;S)=(E^R)^S` literally. On any actual witness
xRySz, canonical quotient transport sends its source class first to
the y-class and then to the z-class, precisely as the composite does.
Seriality gives such a witness from every source class, so

\[
 q_{R;S,E}=q_{S,F}\circ q_{R,E}.
\]

This concerns the SAME intermediate quotient b/F and actual RAW
composition; no mixed-sort commutativity or arbitrary charts are allowed.
The interval contains all invariant equivalences, not only exact kernels
or named coordinate sorts of a later expansion. Neither named exactness
nor a separate noncollapse conclusion follows from this algebra.

## N03: One original quotient label controls every stage of a closed return

**D07/D08; C15–C24.** Let n≥1, let the whole actual typed word return
to the SAME sort a0, and assume `P1;...;Pn⊆E0`. Define R0=Id,
`Ri=P1;...;Pi`, suffix `Si=P(i+1);...;Pn`, and Sn=Id. All prefixes
and suffixes are serial/co-serial, including identity endpoints and
repeated original sorts.

For a point y at position i choose xRi y and label it `[x]_E0`.
If xprime is another predecessor, choose ONE suffix witness ySi z.
Both starts reach z through the entire word, so
`x E0 z E0 xprime`. The label is canonical. This simultaneously proves
`Ri;Riᵗ⊆E0` rather than assuming the prefix kernel conditions.
Seriality/co-seriality give an equivariant onto map λ_i to the ONE
fixed original quotient a0/E0. Its literal kernel is

\[
 E_i=R_i^{\smile};E_0;R_i.
\]

For every actual y Pi z, choose a prefix predecessor of y. It is also
a prefix predecessor of z one stage later, so
`λ_(i-1)(y)=λ_i(z)`. Consequently `Pi;Piᵗ⊆E_(i-1)`. To get the
exact next transported kernel, choose predecessors of arbitrary z,zprime;
equality of their λ_i labels is exactly E_(i-1)-equivalence of those
predecessors. Thus `Piᵗ;E_(i-1);Pi=Ei` in BOTH directions.

Let bar-λ_i be the induced bijection from a_i/Ei to a0/E0. The actual
edge transport is therefore

\[
 q_i=\bar\lambda_i^{-1}\circ\bar\lambda_{i-1}.
\]

At position zero the label is the original E0 quotient map. At the final
position, xRn y implies x E0 y, so the label is AGAIN the very same
quotient map on the SAME endpoint carrier. In particular En=E0.
All intermediate label bijections cancel in the composite; the remaining
endpoint maps agree, giving literal identity on a0/E0. There is no
groupoid section, origin system or independent chart selection.

For EVERY invariant J≥E0, compose ALL λ_i with the canonical projection
a0/E0→a0/J. These maps are still equivariant and onto. Their kernels
are simultaneously `Ji=Riᵗ;J;Ri`; edge-label equality and the identical
endpoint labels give the same factor transport and whole-loop identity
on a0/J. This construction is compatible with coarsening projections.
Generic J and Ji need not be named exact coordinate sorts or definable.

## N04: First-order definability is a separate source-context conclusion

**C13/C14/C25/C26.** The algebra above is valid for arbitrary actual
transitive group actions. It gives invariant equivalences. First-order
definability requires formulas for the relations and base equivalences:
converse, finite composition and the expression `Rᵗ;E;R` then have
first-order formulas by finite existential quantification. The same
applies to each finite return prefix and Ei, and to Ji IF J is definable.

In the intended original finite complete atomic homogeneous source, the
group G is the FULL original automorphism group, and its finitely many
pair orbitals between the relevant named sorts are named.
Every invariant binary relation or equivalence is a finite disjunction
of those names, discharging the definability gate A03. The source
definability wording is therefore valid in that application. State this
context explicitly when extracting the more general group-action lemma.

The generic core and return branches have no A03 dependency. Their source
exports add C13 or C25 for the definability conclusion, while arbitrary
invariant coarsenings remain valid without a definability claim.
This is an explicit context qualification, not a new gap in the intended
finite-orbital source. No source TeX is changed.

## N05: Every prescribed compatible group element can be lifted on points

**D09; C27–C32.** Let rho:K→Gamma be a homomorphism and pi:Y→B an
equivariant surjection, Y nonempty. This is an independent action problem;
neither group action needs to be faithful or transitive.

Assume rho is onto and its kernel is transitive on every actual pi-fibre.
For a compatible request `γ pi(x)=pi(y)`, first lift γ to k0. Then
pi(k0 x)=pi(y). Choose a kernel element h sending k0 x to y and put
`k=h k0`, with correction on the LEFT for left actions. It has exactly
the prescribed group image and prescribed point value. The choice may
depend on the request; no coherent or homomorphic section is required.

Conversely assume every compatible prescribed point request can be met.
For arbitrary γ choose x in nonempty Y, and by surjectivity choose y
above γ pi(x). Its lift proves rho onto. Taking γ=1 for same-fibre x,y
proves kernel transitivity. In a nonfaithful action a prescribed group
element is still an ELEMENT, not merely its induced permutation.

For a concrete positive example, let rho:C4→C2 be reduction mod 2 and
let Y=B=C2, pi identity, K acting via rho and Gamma regularly. Kernel
fibres are singletons and the property holds, while K acts nonfaithfully
and this group epimorphism has no homomorphic section: an odd element of
C4 cannot have order dividing two.

These proof claims document existing shared B001 point-lifting support.
Receiving implementation ownership and consumer imports are unchanged.

## N06: Saturate the FULL root orbital, then restrict to real diversity

**D10/D11; C33–C37.** Let tau and sigma be equivariant surjections from
transitive nonempty roots A,B, either the same sort or disjoint, and let
Theta be ONE output pair orbital. Surjectivity gives a root witness
(x0,y0), possibly diagonal, and let O be its FULL root pair orbital.

For any (x,y) in the output-orbital pullback, ONE g sends the witness
output pair to its output pair. Equivariance gives
`x J gx0`, `(gx0,gy0)∈O`, `gy0 K y`, so the pair lies in `J;O;K`.
Conversely changing either representative inside its actual kernel
leaves its output unchanged; the O pair has output in Theta. Hence

\[
 P_\Theta=J;O;K.
\]

The proof works for ANY root witness. Every root orbital maps onto
exactly one output orbital; thus these full pullbacks partition the
root product into unions of whole root orbitals. Restrict that partition
to the invariant real diversity set `D={(x,y):x≠y}` and discard empty
parts. This partitions both D and the set of root orbitals inside D.
For disjoint roots D is the whole product.

Crucially, saturation is equality-inclusive BEFORE restriction. A diagonal
root orbital may saturate to a relation containing diversity. An
off-diagonal root orbital may saturate back to a relation containing
diagonal pairs. Therefore compute `(J;O;K)∩D` at the END; do not remove
equality from O first, and do not confuse real-root diversity with output
sort equality. No positive/strong word realization theorem is used.

## N07: Classify the unique possible empty-diversity output orbital

**D12; C38–C44.** If the diversity pullback of Theta is empty, its full
pullback is still nonempty. It contains some equal-coordinate pair
(x,x), so the equal-or-disjoint convention forces A=B. If J is not
identity, root transitivity makes every J-class have at least two points.
Choose xprime≠x in its J-class; changing the first representative keeps
(xprime,x) in the pullback, contradicting empty diversity. The same
argument on the second coordinate forces K=Id too. Both surjective
coordinate maps are therefore bijections.

The G-orbit of `(tau(x),sigma(x))` is exactly
`{(tau(z),sigma(z)):z∈A}`, by root transitivity. Since this pair belongs
to Theta, that graph IS Theta. Output sorts may be different: this is
the graph between two bijective coordinate copies, not necessarily
logical equality in an output sort.

Conversely if roots coincide, both maps are bijective and Theta is this
graph, membership of a root pair means its outputs equal the outputs of
some same point z. Injectivity forces both roots to be z. The full
pullback is exactly Id_A and its diversity part is empty. The graph is
uniquely determined by tau and sigma, so at most ONE output orbital has
empty diversity pullback. With nonidentity kernels or disjoint roots
there is none.

This proves the full shared B001 orbital API, including its already
requested exception. The package adds explicit proof preparation; it
does not reallocate that API or silently change existing consumers.

## N08: Boundary examples, ownership and diagnostic limits

**C12/C32/C45–C50.** Invariance does not imply first-order definability
for an arbitrary chosen group action. On the pure equality structure
with carrier Z, the translation subgroup is transitive and preserves
parity equivalence. That equivalence is not preserved by all pure-set
automorphisms, hence is not parameter-free definable. With R=Id its
transport is itself. This example lies outside A03; finite named original
orbitals discharge that gate in the intended source.

Empty R has vacuous kernel containment but no quotient labels. Without
transitive endpoints a nonempty invariant relation can miss target
vertices. With full R on two-point endpoints and E=Id, the kernel
condition fails and one target has two E-class predecessors. Universal
R with universal E gives singleton quotients; no extra noncollapse is
part of the generic theorem.

The graph of a nonzero translation on a regular cyclic action, with
E0=Id, has nonidentity return map when the actual whole word is not
contained in E0. In valid data the label-induced quotient maps compose
to identity; arbitrary unrelated edge bijections are not replacements
for those maps. No commutativity assumption is hidden in the proof;
the finite controls include a noncommutative S3 action and return.

With constant coordinate maps on one root set, choose the diagonal
root orbital. Its full kernel saturation is A squared with diversity,
whereas removing its diagonal before saturation would give empty.
Saturating a diversity orbital can likewise add diagonal pairs.

If Y=B are empty, the point-lifting request is vacuous and cannot force
rho onto. If pi is not onto, take Y singleton, B the regular two-point
C2-set, K trivial and pi selecting one point. The only tested compatible
gamma is identity, so the request property holds while rho misses the
other element. Onto rho without fibre-transitive kernel also fails, as
seen on two parallel copies of one base action with trivial kernel moves.

The control script computes finite relations, actual quotient classes,
lattice operations, return maps, prescribed group ELEMENT lifts, and full
orbital saturations independently. These finite diagnostics establish no
unbounded theorem, first-order definability, exactness, SAP/CCO or Lean
proof. All 93 frozen source hashes, existing consumers, shared B001
allocation, five HN/HKN receiving bindings and provider-cache plan stay
unchanged. Overall EPPA remains source-relative.
