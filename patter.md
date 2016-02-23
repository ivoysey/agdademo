ntro
=====

hi! for the couple of people in here that don't know me, i'm ian
voysey. thank you all for coming!

today i'm going to give you a taste of what it's like to use agda to prove
some theorems about functional programs.

you can find the source for everything i'm doing (and embarrassingly most
of the words that i'm saying right now) on github at
http://github.com/ivoysey/agdademo

there a few things that i'm specifically _not_ going to do, so let's get
that out of the way:

  - there's a lot of really interesting work happening right now using agda
    to formalize some of the developments in HoTT, or using HoTT and Agda
    together to produce new ways formalize other things. i'm not going to
    talk about that at all.

    if the technical details mean something to you, i'm pretty much going
    to stay entirely inside `Set`. there's nothing higher dimensional
    happening here, even though most of it probably works in that more
    general setting.

    i think it's better to have a really good understanding of agda as a
    tool before trying to use it to work on HoTT as a domain. doing that
    requires that you use some of the more arcane features of the language,
    which is exciting but not a great place to start.

    for more information about that, talk to me later or to the real
    experts that are patient enough to help me when i'm stuck: favonia,
    evan cavallo, ed morehouse, carlo angiuli, and dan licata.

  - i'm also not going to start at the very beginning. there will be
    language features that i gloss over here that deserve a much more
    careful treatement. my goal is not to prove the highly novel fact that
    addition on `Nat` is commutative to you, or really go into a careful
    discussion of Agda syntax, but to show you why it's beautiful to work
    in Agda.

    there are a bunch of tutorials that take that careful syntactic
    approach on the Agda wiki and around the internet.

    a really great resource to start with from here is dan licata's agda
    course from Wesleyan. he's offered access to anyone at cmu that wants
    to see the materials if you shoot him an email. if you have nothing
    else to do for a week, i emphatically reccomend it.

    you can also check out the videos and assignments from the OPLSS13
    course that dan and i gave. there's some overlap with his work at
    Wesleyan; that came after OPLSS so the presentations of the things in
    the intersection are generally better there.

    this also means i'm not going to talk about the std lib (there's
    several competing versions) and will end up reimplementing a little bit
    of it as a result. to minimize that, i'm going to avoid using some
    natural language features like pairs.

style of approach
-----------------

the compelling thing about agda is that it's both a full-throated
dependently typed functional programming language and a proof assistant. so
it's natural to write the programs you know and love and then demonstrate
things about them.

  - generally speaking, this is called _extrinsic verification_, in that we
    stick to simple types for the programs themselves and then once they're
    complete demonstrate that what we're interested in are true. i think of
    this as doing the best version of the thing we all know.

  - the other option is _intrinsic verification_, where we use elegant
    dependent types to make the programs themselves demonstrate the
    properties that we want of them.

there's a real tension between these two approaches, and it's an
interesting software engineering effort to find the right place on the
spectrum for a given program.

example
*******

a good first example to think about is the difference between defining
insertion sort on lists and showing that it produces sorted lists versus
defining the type of _sorted lists_ and giving roughly the same insertion
sort code richer types to show that it maps into that richer type.

if all you want to do is show sortedness, you'd quickly notice that the
proofs in the extrinsic style approach are more or less the same as the
code itself. this is strong evidence that an intinsic approach might be
helpful, and if you then tried it you'd find that the code more or less
doesn't change and you can just enrich it with this stronger type that
holds sortedness to be self-evident.

the problem is that just knowing that the output of an algorithm is sorted
isn't enough to argue that it's a sorting algorithm---you also need to know
that the output is a permutation of the input. to update your intrinsic
implementation you have to rewrite most of the types to add this new
property, and that may or may not be a lot of clutter.

it turns out that it'll actually be quite hard to make an insertion sort
that intrinsicially demonstrates the permutation property: it's easy for
sortedness becasue the inductive definition of sortedness is inherently
structurally recursive; the inductive definition of permutations is not, so
it's a bad match for the pattern of recursion that the algorithm follows,
and therefore will induce a lot of lemmas.

on the extrinsic side, you don't have to touch the code of the algorithm,
but you may well need to reimplement a lot of things. if you consider also
showing that your implementation is or isn't stable, that might be easy to
do intrinsically, so doing it extrinsically will be a lot of repeated work.

there is no silver bullet to this sort of question; it's part of the art
and engineering of formalization.


you can check out some beautiful examples of both styles in Dan's course
work.

today i'm going to focus pretty much only on extrinsic verification only
because it shows how to use the tool with a little less overhead. but don't
get the wrong idea that this is the only way to skin this cat.


actual tutorial
===============

alright, let's get cracking!

defining simple types and functions
-----------------------------------

here's the familiar type of lists:
```agda
  data List (A : Set) : Set where
    [] : List A
    :: : A → List A → List A
```

note that, unlike SML or other functional langauges, agda is quite
explicit about polymorphism. you have to give a name to the type variable
over which a definition is polymorphic. technically what we're doing is
defining a family of types that's indexed by the type `A`.

once you have a type, it's easy to define the familiar functions on that
type by recursion and pattern matching. for example, this is the standard
structurally-recursive append:

```agda
  ++ : (A : Set) → List A → List A → List A
  ++ A [] l2 = l2
  ++ A (:: x l1) l2 = :: x (++ A l1 l2)
```

technically, again, we're defining a family of functions indexed by the
type `A`: `(name : type2) → type2` is the Agda notation for Pi types.

i should note that there's no reason for `++` or `::` to be curried
especially. throughout this demo i'm going to avoid using pairs and Sigma
types. the treatment of them is solid, but it's a little bit of syntax that
i'd prefer to avoid, so i'm just going to curry everything.

the features that i used to write that function live that doesn't show up
statically in this file are goal, querying goal types, and automatically
casing. we'll use all of them pretty much constantly.

this is a perfectly adequate definition, but it would get tiresome in a
practical context for a couple of reasons:

  - we prefix pretty much everything, including cons

  - we have to carry around the type A everywhere and we never do anything
    with it

we can fix the first complaint by using Agda's notion of _mixfix_
identifiers: whenever `_` appears in any identifier, it stands for the next
argument read off the type in left to right order. so we rewrite the type
of lists to

```agda
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A
```

which indicates that we intend to use `::` in between its two
arguments. this isn't just infixing; you can have as many `_` as you want
and they can start the identifier to get you post-fix notation. (we'll see
more of this as we go.)

using this type, we can then rewrite append in a more familiar shape

```agda
  ++ : (A : Set) → List A → List A → List A
  ++ A [] l2 = l2
  ++ A (x :: l1) l2 = x :: (++ A l1 l2)
```

the second complaint still abides, though. we solve it by making the
argument `A` _implicit_:

```agda
  ++ : {A : Set} → List A → List A → List A
  ++ [] l2 = l2
  ++ (x :: l1) l2 = x :: (++ l1 l2)
```

the `{ }` syntax is more or less like the `( )` for Pi types, except that
you're allowed to leave it off at the call site and agda will guess what
you meant from the context. when i say "guess", i mean that it's basically
just doing a form of unification, so it dos pretty well.

picking which order to put your arguments and what to make implicit or not
is an art---never using it is irritating, using it too much is so cluttered
as to be un-damn-readable, and there's a shifting sweet spot in
between. it's a bit like choosing which arugments to curry and in what
order.

we can use the mixfix mechanism for any identifier, not just in types
or type constructor names:

```agda
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)
```

identity type
-------------

before we can prove anything interesting, we need a notion of identity, so
that we can even begin to make statements like "x is y". there is a whole
lot of interesting discussion about what this should be and why. let's not
worry about it too much  this is a perfectly good definition:

```agda
  open import Agda.Primitive using (Level; lzero; lsuc)

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
     refl : M == M
  infixr 9 _==_

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL refl #-}
```

(the `infixr` keyword is just syntactic sugar to let us leave off
parenthesis later. a mix-fix identifier that _happens_ to be infix can be
assigned binding precendence and directionality.)

there's some technical junk going on here, about levels, that you don't
need to worry about. i'm including it because it lets us associate our
definition with agda's built in equals, with that `{-# BUILTIN ... #-}`
junk, which lets us avoid having a lot of irritating lemmas.

this introduces identity as just another type family--it's not in a
different syntactic category to lists or somethingw weird. we can compute
on identities pretty much like normal and show that they have the
properties we'd expect.

again there's a lot more going on here, and i'm just including a practical
fragment.

```agda
  --- identity is transitive..
  _·_ : {α : Set} {x y z : α} → x == y → y == z → x == z
  refl · refl = refl

  --- .. and symmetric
  ! : {α : Set} {x y : α} → x == y → y == x
  ! refl = refl
```

the one slightly non-traditional property of identities that we'll get a
lot of milage out of is usually called `ap`. it states that everything else
we can hope to define respects this notion of identity. think of this as a
tool for swapping out an expression for one to which it's
identified---exchanging like for like:

```agda
  ap : {α β : Set} {x y : α} (F : α → β)
          → x == y → F x == F y
  ap F refl = refl
```

first theorem: `++` is associative
----------------------------------

alright, let's prove something!

```agda
  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] [] [] = refl
  ++assoc [] [] (x :: c) = refl
  ++assoc [] (x :: b) [] = refl
  ++assoc [] (x :: b) (x₁ :: c) = refl
  ++assoc (x :: a) [] [] = ap (_::_ x) (++assoc a [] [])
  ++assoc (x :: a) [] (x₁ :: c) = ap (_::_ x) (++assoc a [] (x₁ :: c))
  ++assoc (x :: a) (x₁ :: b) [] = ap (_::_ x) (++assoc a (x₁ :: b) [])
  ++assoc (x :: a) (x₁ :: b) (x₂ :: c) = ap (_::_ x) (++assoc a (x₁ :: b) (x₂ :: c))
```

this shows off the real power of agda's strutured editing. because the
editor is aware of the types we've defined, we can generate all the cases
of a proof and query the exact thing we need to show in each case and then
just hammer through the cases. we get slightly odd names for things
sometimes, but nothing insurmountable. (you can often carbon date agda code
by the syntax of the auto-generated names.)

sometimes this is great, and sometimes it means that you do a lot more work
than needed to end up producing something hard to read. in this case, note
that we do fundimentally the same thing in the latter four cases: we note
that you can swap equals for equals in the second argument of a `::` and
then recurr on `a` with the other lists unchanged.

a tighter proof, then, only cases on `a`

```agda
  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] b c = refl
  ++assoc (a :: as) b c = ap (_::_ a) (++assoc as b c)
```

which reveals that this really is a proof by structural induction on just
one list---perhaps unsurprisingly because of how `++` is implemented.

the problem here, at least for my money, is that this makes a ton of sense
dynamically while we're writing it, but i have a really hard time looking
back at it five minutes later and remembering how the proof went.

this matters once you start building up more proofs that rely on one
another. if you mention a previous proof in the type of a subsequent one,
you're not saying "oh any old proof of type Tau"--you're saying *this
specific proof*. so you may well need to argue about the exact bit of
evidence your previous work coughs up, and therefore you need to understand
it.

the solution to this complaint is a beautiful (read: groan inducing) use of
mix fix notation: we can define a notation for linking together a bunch of
appeals to transitivity. that lets us write the end points of each step
explicitly in the program text, even when agda doesn't need them:

```agda
  -- mixfix doesn't define precedences
  infix  2 _■
  infixr 2 _=<_>_

  _=<_>_ : {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
  _ =< p1 > p2 = p1 · p2

  _■ : {A : Set} (x : A) → x == x
  _■ _ = refl
```

we can then go back and write that proof in a much more explicative style:

```agda
  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] b c = refl
  ++assoc (a :: as) b c with ++assoc as b c
  ... | ih = ((a :: as) ++ b) ++ c   =< refl >
              (a :: (as ++ b)) ++ c  =< ap (λ x → a :: x) ih >
               a :: (as ++ (b ++ c)) =< refl >
              (a :: as) ++ (b ++ c)  ■
```

contrast this sort of proof to something that you might see in Coq ---
there's a lot more writing in the sense that i'm sure that there's some
tactic that would do this for us, but it's much easier to use this proof
term as a way to explain things between people.

this also lets us get a handle on exactly when agda wants to reduce
expressions. it's a little inconsistent with this, especially between
versions of agda and under small changes to your program text.

worse, sometimes the reductions go beyond the point where you had a lemma
that you wanted to apply. this can make the type that appears in the goal
seem impossible to fulfill, or like it's not something your lemma can
handle, because agda's busily doing its best impression of a freshman and
just applying evaluation rules whenever it feels like it.


`foldr` and `foldl`
-------------------

alright, so that's about all we'll need to know about agda syntax for the
rest of today. i want to shift gears and go through a little larger of a
proof about some specific functional programs to give you a feel for what
it's like to have an idea and then develop it and understand it by playing
with the theorems in agda.

recall the familiar functional programs

```agda
  foldr : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldr f b [] = b
  foldr f b (x :: l) = f x (foldr f b l)


  foldl : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldl f b [] = b
  foldl f b (x :: l) = foldl f (f x b) l
```

what can we say about how they relate to eachother?

the moderately insane description of these we get from most sources,
including this direct quote from the SML basis library documentation is

```
foldl f init [x1, x2, ..., xn] returns
     f(xn, ... , f(x2, f(x1, init))...)
  or init if n = 0

foldr f init [x1, x2, ..., xn] returns
     f(x1, f(x2, ..., f (xn, init)...))
  or init if n = 0
```

so the common relation you'll hear is that they're just reassociations of
one another, that `f` is associative, commutative, and that `b` is a unit
for it then they do the same thing.

this doesn't actually make a lot of sense, and is kind of a pet peeve of
mine: all three properties are normally only defined on `A x A -> A`.  the
weak answer is to restrict `f` to a lower type and use these canonical
properties, but then we're not really working with the functions as given.

here's a different way to think about it:

`foldr` is the HOF that abstracts the pattern of structural recursion on
lists; `foldl` is the HOF that abstracts the pattern tail recursion. the
relationship between them is that they apply their functional argument in
the opposite order---`foldl` eagerly applying as soon as there's anything
in scope that's the right type, `foldr` doing the structural thing
following the type directly. if that order doesn't matter for `f`, they do
the same thing.

that is to say that under some condition, we should be able to write a
program at type

```agda
  foldlr : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                {! something about f !} →
                foldr f b L == foldl f b L
```

the reason we usually talk about associativity and commutativity is that
they give us some sense in which we can move arguments around in that big
expression. so let's think of a property for `f` that _does_ make sense
with respect to its real type but still has the "move the arguments
around!" flavor to it and type checks. there's kind of only one choice:

```agda
  f a (f b c) == f b (f a c)
```

happily, it's easy to check that if `A` and `B` are the same and `f` is
commutative and associative then it also has this property, so that's
another sign that we're on the right track. (we'll see a proof of this
later on, as an example of doing something less inductive in Agda.)

restating our theorem, we get

```agda
  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                foldr f b L == foldl f b L
```

naming the proof term of this property Δ. (if you know a better name,
please tell me. i just think Δ looks kind of exciting.)

so let follow our noses and try to prove it!

```agda
  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                foldr f b L == foldl f b L
  foldlrΔ f b [] Δ = refl
  foldlrΔ f b (x :: L) Δ with foldlrΔ f b L Δ
  ... | ih = foldr f b (x :: L) =< refl >
             f x (foldr f b L)  =< ap (f x) ih >
             f x (foldl f b L)  =< {! ruh roh !} >
             foldl f (f x b) L  =< refl >
             foldl f b (x :: L) ■
```

(here in the demo, i used the _=<_> notation to work from both sides
towards the middle, which is a great technique)

the type of that unfilled hole is

```agda
  f x (foldl f b L) == foldl f (f x b) L
```

which doesn't even look especially true--until you remember Δ. there isn't
much else we could have done while still following our noses and the shape
of the types invovled, so this is pretty much a dead end.

let's make a lemma and try to jump that exact gap

```agda
  foldl-comm : {A B : Set} (f : A → B → B) (x : A) (b : B) (L : List A)
                      (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                      f x (foldl f b L) == foldl f (f x b) L
  foldl-comm f x b [] Δ = refl
  foldl-comm f x b (y :: L) Δ with foldl-comm f x b L Δ
  ... | ih = f x (foldl f b (y :: L)) =< refl >
             f x (foldl f (f y b) L)  =< ap (f x) (! (foldl-comm f y b L Δ)) >
             f x (f y (foldl f b L))  =< Δ x y (foldl f b L) >
             f y (f x (foldl f b L))  =< ap (f y) ih >
             f y (foldl f (f x b) L)  =< foldl-comm f y (f x b) L Δ >
             foldl f (f y (f x b)) L  =< refl >
             foldl f (f x b) (y :: L) ■
```

this goes through, so that finishes the proof!

```agda
  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c)) →
                foldr f b L == foldl f b L
  foldlrΔ f b [] Δ = refl
  foldlrΔ f b (x :: L) Δ with foldlrΔ f b L Δ
  ... | ih = foldr f b (x :: L)       =< refl >
             f x (foldr f b L)        =< ap (f x) ih >
             f x (foldl f b L)        =< foldl-comm f x b L Δ >
             foldl f (f x b) L        =< refl >
             foldl f b (x :: L)       ■
```

a confession
------------

it's a little hard for me to say why this is the right lemma other than it
comes up and we happen to be able to prove it. but i can motivate it with a
confession: this proof was about a hundred lines longer until late last
week.

the intuition i have for why this theorem is true at all comes from
thinking about that crummy picture. look at it and you'll see that there is
a *specific* list that these things agree on.

that is to say, `foldr` and `foldl` don't just apply `f` to the elements of
their arguments in different orders, they do so in _exactly the opposite
order_ so they meet in the middle: at the reverse of the input list.

we can define reversing just like always:

```agda
  rev : {A : Set} → List A → List A
  rev [] = []
  rev (x :: l) = rev l ++ (x :: [])
```

then state that rough intuition a little more precisely as

```agda
  foldlrrev : {A B : Set}
              (f : A → B → B)
              (b : B)
              (L : List A) →
              foldr f b L == foldl f b (rev L)
```

and then restructure the proof to

```agda
  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                foldr f b L == foldl f b L
  foldlrΔ f b L Δ =
        foldr f b L       =< foldlrrev f b L >
        foldl f b (rev L) =< {! something here !} >
        foldl f b L       ■
```

if you try to prove `foldlrrev` by induction, you'll find that you need to
know how foldl distributes over an append, because of how `rev` is defined

```agda
  foldl++ : {A B : Set}
            (f : A → B → B)
            (b : B)
            (L1 L2 : List A) →
            foldl f b (L1 ++ L2) == foldl f (foldl f b L1) L2
```

then to fill that last gap in the main proof you need something at type

```agda
  foldlΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                foldl f b L == foldl f b (rev L)
```

the proof of this leads naturally to the `foldl-comm` lemma --- which also
applies perfectly well without the detour through `rev`.

the connection between the two is that in the proof of `foldl-comm`, you
effectively _reimplement `rev`_ at the place where you apply Δ, but in a
pretty opaque way.

this other proof is done out in full in the agda file, for the curious.

at `A x A → A`
--------------

as a final note, we can circle back around and note that the Δ property
really is what you'd want. so let's say in some larger proof you wanted to
make your life easier and swap in a `foldl` for a `foldr` summing a list of
natural numbers. if you prove that addition is associative and commutative
(spoiler: it is) then you could use

```agda
  -- Δ really is a generalization of the thing people usually say
  assoc-comm-Δ : {A : Set}
                 (_⊕_ : A → A → A)
                 (assoc : (a b c : A) → ((a ⊕ b) ⊕ c) == (a ⊕ (b ⊕ c)))
                 (comm : (a b : A) → (a ⊕ b) == (b ⊕ a)) →
                 ((a b c : A) →  (a ⊕ (b ⊕ c)) == (b ⊕ (a ⊕ c)))
  assoc-comm-Δ _⊕_ A C a b c = a ⊕ (b ⊕ c)    =< ! (A a b c) >
                               (a ⊕ b) ⊕ c    =< ap (λ x → x ⊕ c) (C a b) >
                               (b ⊕ a) ⊕ c    =< A b a c >
                               b ⊕ (a ⊕ c)    ■
```

to cough up a Δ and then apply the proof above to get the equality you're
interested in. this example also shows off the `=< >` notation in a little
more general of a setting; i would have gotten a much better grade in
Algebraic Structures Theory in Agda than on paper.
