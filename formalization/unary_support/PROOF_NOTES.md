# B034 — local supports and actual unary-generated diagrams

Frozen mathematical source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
This expands two results in
`sections/binary_unary_irreducible_local_cover.tex`. Ten definitions,
32 proof claims and six tasks are preparation contracts, not Lean code.
There are no mathematical provider imports or external HN theorem calls.
The source TeX remains unchanged.

There are two independent branches. The local-support branch assumes total
unary functions and relations of arity at most two. The HN branch permits
initially partial unary functions and arbitrary relation arities; it uses
domain-reflecting induced inclusions and actual completed class membership.
Neither argument assumes the whole input has a completion.

## N01: Partial unary closure and actual induced inclusions

**D01–D03; C01–C04.** Regard a named unary function as a typed partial map.
For a subset B, a vertex belongs to `cl_C(B)` when a finite chain of
already-defined function values starts at a point of B and ends at that
vertex. The empty chain includes each generator. A chain never supplies an
undefined value or changes a sort tag without the corresponding symbol.

Every closed subset containing B contains every such chain, by induction
on length. The reachable subset itself is closed: append the applicable
already-defined transition. This proves the least-closed-subset property.

An induced embedding of partial-function structures reflects applicability
domains as well as relations. If it retains x and f is defined at x in C,
then f must be defined in the substructure and its actual value must remain
there. Conversely, a closed subset, with exactly the ambient relations,
domains and values on its points, has an induced embedding into C.
This is stronger than taking a restriction of the function graph and
allowing it to forget an outgoing value.

Intersections of closed subsets are closed. More specifically to UNARY
operations, arbitrary unions of closed subsets are closed: a defined value
has a single starting point, which belongs to one of the union's members.
Consequently

\[
 \operatorname{cl}_C(B)=\bigcup_{x\in B} U_x,
 \qquad U_x=\operatorname{cl}_C\{x\}.
\]

There are no constants, so the empty union is closed and the empty
generator set has empty closure. This equation would generally fail for
binary operations; see N07.

For closed induced D inside C, every defined chain beginning in D stays in
D, and the domain/value at each step agrees with C. Therefore
`cl_D(B)=cl_C(B)` for B contained in D. The two supports have identical
induced relation interpretations as well. No completion or isomorphism
choice is involved in this equality.

Use free-amalgam irreducibility in the actual partial signature: two
proper induced closed factors, covering D and sharing their induced
intersection, cannot have diagram union exactly D. The common base is
allowed to be empty. Whether the empty object itself is called irreducible
is a separate convention, relevant in N03 and N07 only.

## N02: Omission unions give an exact free decomposition

**D04–D05; C05–C10.** In this branch all unary functions are total and each
relation has arity zero, one or two. Form H(D) from all singleton closures
and the endpoint closure of each displayed off-diagonal binary tuple.
Each support retains its entire induced diagram, not just its generating
relation. Equal supports need not be listed twice.

Every point belongs to a singleton support; its unary function values,
unary predicates and diagonal binary tuples are supported there. A
displayed binary tuple on distinct points belongs to its designated
two-generator support. Nullary truth is unchanged by every induced
restriction, including an empty restriction.

Fix distinct x,y in an induced closed irreducible D and suppose no support
contains both. Set

\[
 A_x=\bigcup\{U\in H(D):y\notin U\},\qquad
 A_y=\bigcup\{U\in H(D):x\notin U\}.
\]

The singleton closure of x avoids y, so it belongs to the first union.
Every member of the second union avoids x. Thus `x in Ax \ Ay`;
symmetrically `y in Ay \ Ax`. Both factors will be proper. Each union is
closed by C03, and their intersection is closed by C02.

Every support omits at least one of x,y, hence occurs wholly in at least
one union. Since singleton supports cover every vertex, `D=Ax union Ay`.
Every off-diagonal binary tuple is contained in one support and therefore
wholly on one side. For unary tuples and diagonal binary tuples use a
singleton support. Every unary value remains in either side containing its
argument by closedness. Nullary diagrams agree in both induced factors and
in the induced overlap.

It follows that the free amalgam of the induced closed restrictions to Ax
and Ay, over their entire induced intersection, has exactly D's vertices,
relations, applicable function domains and function values. There is no
extra cross-side tuple. Both factors are proper by the exclusive witnesses
x and y. This contradicts irreducibility, even when the intersection is
empty. Therefore each distinct pair in a nonempty irreducible D belongs
to some H(D) support. The singleton case is vacuous.

## N03: Local induced embeddings and the empty/nullary gate

**D06; C11–C18.** Suppose f satisfies the source homomorphism/local embedding
premises. If D is closed and induced in C, N01 identifies each H(D) support
with the corresponding actual H(C) support. The restriction of f is
therefore an induced embedding on it for EVERY relation symbol and all
function domains/values.

For distinct x,y in a nonempty irreducible D, N02 supplies a common local
support. Its injectivity gives `f(x)!=f(y)`, proving injectivity on D.
For any target binary tuple `R(f(x),f(y))` on distinct x,y, the same kind
of support reflects R into D. The support need not have been generated by
an R-tuple: its induced embedding reflects all symbols. This is why a
missing tuple may legitimately be reflected using a support generated by
a different displayed relation or a unary closure.

For a unary predicate at f(x), or a repeated-coordinate binary tuple
`R(f(x),f(x))`, use the singleton closure of x. For a nullary relation and
nonempty D, choose any x and use its singleton support. Its induced
nullary interpretation is the same as D's. All relation reflection cases
are now explicit. Sorts, displayed relations and total unary functions
were already preserved; their restrictions to closed D have the same
total domains. Thus f embeds each NONEMPTY source irreducible, C16–C17.
The source's complete-target premise is retained but unused by this proof.

To say this for EVERY admitted irreducible, C18 records A07 explicitly:

- If irreducibles are defined nonempty, there is no additional case.
- With positive relation arities, the empty restriction embeds vacuously.
- With nullary relations and empty irreducibles, the empty restriction
  needs nullary truth agreement. If C is nonempty this agreement already
  follows from any singleton local embedding. For empty C it must be
  required separately, or follow from a fixed nullary diagram convention.

The literal combination of an empty source, arbitrary nullary truth and
empty irreducibles is a counterexample to the source's unrestricted final
wording. C17 does not require any repair; C18 is deliberately gated. This
is recorded as article feedback F01 rather than silently strengthening a
global signature convention. No source TeX is changed.

## N04: One-generated partial diagrams are irreducible before K is used

**D07; C19–C20.** Return to the general partial-unary language. There is no
relation-arity restriction and no premise that functions of C are total.
The induced closure U_x is made from the already-defined chains in N01.

Suppose U_x is a free amalgam of two proper induced closed factors. Their
union covers x, so one factor contains x. That factor is closed under
every already-defined unary value. Induction along a chain from x forces
it to contain every vertex of U_x, contradicting properness. In fact this
argument precludes a cover by two proper closed factors even before their
relations are checked. Empty-base conventions cause no issue here because
U_x contains x. This proof uses neither K nor totality nor a size bound.

Only AFTER C19, apply the hypothesis that every irreducible induced
substructure of C is an ACTUAL member of K. This gives U_x in K as its
existing full induced diagram. If K is described only up to isomorphism,
the same inference is valid when class membership is isomorphism-closed;
do not silently change membership otherwise.

Actual membership retains the whole existing diagram, beyond a
homomorphism or a later completion into a completed member. The singleton
undefined-function example in N07 distinguishes these two weaker assertions
from actual membership. It cannot domain-reflectingly embed into a total
member: such an embedding would already force its function to be total.
An induced embedding alone also does not establish K membership for an
arbitrary K without a hereditary-membership assumption.

## N05: Total unary maps and well-typed one-variable identities

**D08; C21–C23.** For any correctly sorted x and applicable symbol f, the
actual U_x is a completed K member. Thus f is defined at x in that very
structure, and its inclusion into C preserves the value. Hence f was
already defined at x in C. Quantifying over points and symbols proves
totality throughout C. No quantitative bound is used.

A unary term here means a type-correct composition of named unary
functions applied to a SINGLE variable x. The variable itself is the
empty composition. Terms t(x),s(x) in an equation have the same output
sort. These conventions retain identities such as `g(f(x))=x` across
named sorts.

Induct on term construction to evaluate it inside U_x. The initial x is
present; each next value is present by closedness and completed totality.
The induced inclusion makes each evaluation agree literally with C.
If `t(x)=s(x)` holds in all K members, it holds in actual U_x; both sides
are therefore equal in C at x. Empty input sorts make the pointwise
assertion vacuous.

An equation with independent variables, such as `t(x)=s(y)`, is not
covered. A unary operation language alone does not make every equation a
one-variable identity. See the two-point identity-function counterexample
in N07. No identity, relation, or completedness of the WHOLE C is inferred
merely from local K membership beyond the stated conclusions.

## N06: Conditional closure bounds and full-diagram admissibility

**D09–D10; C24–C29.** The actual U_x remains one-generated when viewed as a
completed K member. Its vertices are exactly the chains from x, and C20
has supplied no additional values, vertices or relations: it recognized
membership of that existing diagram. Closure inside U_x and C agrees by
C04. Therefore any supplied bound m on completed one-generated K members
applies to U_x, giving `|U_x|<=m`.

Use the unary closure union from C03 for a finite B. Finite union
cardinality is at most the sum of the cardinalities, so

\[
 |\operatorname{cl}_C(B)|
 \le\sum_{x\in B}|U_x|\le m|B|.
\]

Overlaps improve the bound and cause no additional assumption. Empty B
has empty closure and satisfies the inequality. Empty C has vacuous
pointwise assertions. If m is zero and C contained a point x, its closure
would contain x and violate the bound, so these premises force C empty.
No uniform bound for arbitrary completed classes or arbitrary malformed
partial inputs is asserted.

The downstream hidden definition
`sections/v27/10_typed_unary_terms_return.tex`,
`def:typed-unary-admissible-source`, requires the FULL induced generated
hidden diagram to be an actual completed one-generated member, including
internal binary relations as well as functions and literal term equalities.
Choosing K to be that intended completed hidden age, C20/C24 supply exactly
this witness; the identity isomorphism suffices. Totality or identities
alone would be a weaker interface and must not replace it.

This is a local interface theorem. It neither supplies the hidden class's
uniform bound m nor proves a restricted bounded-obstruction theorem, an HN
local-finiteness/Ramsey theorem, or a completion of C. No theorem from the
HN paper is an external provider; the source itself states the required
domain-reflecting convention. There are no mathematical package prerequisites.

## N07: Concrete scope counterchecks

**C30–C32.** Finite controls exercise these boundaries alongside exhaustive
small unary structures; the variants below also have the direct human
arguments given here. They delimit the statements, without proving the
general mathematics.

1. **Empty source and a nullary relation.** Let C be empty and its nullary
   R false. Let H be a singleton with R true; use no functions or other
   relations. The unique map is a homomorphism and there are no local
   supports, so local embedding premises are vacuous. If the empty object
   counts as irreducible, its restriction is not an embedding. Positive
   arities, nonempty irreducibles, or explicit nullary reflection each
   eliminate exactly this problem.
2. **Ternary tuple defeats pair coverage.** On a,b,c put exactly the
   ternary tuple T(a,b,c), with no functions or binary relations. Any free
   decomposition into proper factors loses the tuple, so the structure
   is irreducible; H consists only of singleton supports.
3. **Ternary reflection needs more than pair supports.** Give three points
   a complete irreflexive binary relation E. All pair supports are present
   and the source is irreducible. Add only T(a,b,c) in the target. Identity
   is induced on every singleton and pair yet fails on the full source.
   A complete ternary coloring variant colors tuples with at most two
   distinct entries the same way in both structures and adds a different
   color only on all-distinct triples in the target.
4. **Completability does not mean actual membership.** A singleton with
   undefined unary f can be completed to the identity singleton but is
   not total. Its existing diagram is not that completed K member.
5. **Forgetting domains destroys the independent irreducibility proof.**
   On x,a,b define f(x)=a and g(x)=b, with all other applicable values
   undefined. Its generated closure from x is the whole diagram. Under
   weak graph restrictions it is a free union of restrictions to {x,a}
   and {x,b}; the overlap {x} has both functions undefined. Neither factor
   is an induced domain-reflecting substructure in the present convention.
   This refutes C19 under the weaker convention; it is not presented as a
   counterexample satisfying all the actual-total-K premises.
6. **Two variables do not transfer.** Let K consist of the empty and
   singleton identity-unary structures. The two-point identity structure
   is the free union of its singleton factors, so its only nonempty
   irreducibles are actual K members. The equation x=y is valid in K but
   fails in C. Its two free variables put it outside D08.
7. **Higher function arity changes the result.** On {a,b} define a partial
   binary operation only on the diagonal, with f(a,a)=a and f(b,b)=b.
   This is a free amalgam of completed singleton pieces, so all its
   nonempty irreducibles are actual total singleton members, while mixed
   input domains are missing. Separately, the three-element meet
   semilattice with incomparable a,b and a meet b=c has singleton closures
   {a},{b}, but their pair generates c as well. The unary closure-union
   mechanism is therefore specific to unary operations. The semilattice
   example diagnoses that mechanism; it is not asserted to satisfy the
   whole HN actual-K hypothesis with m=1.

All article feedback is queued for a separately reviewed human pass.
The first source export has an explicit convention gate for its empty
case, while its nonempty claim and the second source result need no such
gate. The private preparation does not release B034, alter public policy,
claim Lean completion, or settle the overall EPPA candidate/HKN bridges.
