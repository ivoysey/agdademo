intro
=====

hi!

for the couple of people in here that don't know me, i'm ian voysey. today
i'm going to give you a taste of what it's like to use agda to prove some
theorems about functional programs.

you can find the source for everything i'm doing (and embarrassingly most
of the words that i'm saying right now) on github at
http://github.com/ivoysey/agdademo

there's two things that i'm specifically _not_ going to do, so let's get
that out of the way:

  - there's a lot of really interesting work happening right now using agda
    to formalize some of the developments in HoTT, or to use HoTT and Agda
    together to produce new ways formalize other things. i'm not going to
    talk about that at all.

    if the technical details mean something, i'm pretty much going to stay
    entirely inside `Set`. there's nothing higher order happening here,
    even though most of it probably works in that more general setting.

    i think it's better to have a really good understanding of agda as a
    tool before trying to use it to work on HoTT as a domain. doing that
    requires that you use some of the more arcane features of the language,
    which is really exciting but not a great place to start.

    for more information about that, talk to me later or talk to the real
    experts: favonia, evan cavallo, ed morehouse, carlo anguili, and dan
    licata.

  - i'm also not going to start at the very beginning. there will be
    language features that i gloss over here that deserve a more full
    treatement. my goal is not to prove to you (the highly novel fact) that
    addition on `Nat` is commutative, or really go into a careful
    discussion of Agda syntax, but to show you why it's beautiful to work
    in Agda for some kinds of problems.

    there are a bunch of great tutorials that take that careful syntactic
    approach on the Agda wiki and around the internet.

    a really great resource to start with from here is dan licata's agda
    course from Wesleyan. he's offered access to anyone at cmu that wants
    to see the materials if you shoot him an email.

style of approach
-----------------

the really great thing about agda is that it's both a full throated
dependently typed functional programming language and a proof assistant. so
it's really natural to write the programs you know and love and then
demonstrate things about them.

generally speaking, this is called _extrinsic verification_, in that we
stick to simple types for the programs themselves and then once they're
complete demonstrate that what we're interested in are true.

the other option is _intrinsic verification_, where we use elegant
dependent types to make the programs themselves demonstrate the properties
that we want of them.

there's a real tension between these two approaches, and it's an
interesting software engineering effort to find the right balance for a
given program. today i'm going to focus pretty much only on extrinsic
verification because it shows how to use the tool with a little less
overhead; you can check out some beautiful examples of both styles in Dan's
course work.


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

note that, unlike SML, agda is pretty explicit about polymorphism. you have
to give a name to the type variable over which a definition is
polymorphic. technically what we're doing is defining a family of types
that's indexed by the type `A`.

once you have a type, it's easy to define the familiar functions on that
type by recursion and pattern matching. this is the standard structurally
recursive append on lists, for example:

```agda
  ++ : (A : Set) → List A → List A → List A
  ++ A [] l2 = l2
  ++ A (:: x l1) l2 = :: x (++ A l1 l2)
```

technically, again, we're defining a family of functions indexed by the
type `A`: `(name : type2) → type2` is the Agda notation for Pi types.

the features that i used to write that function live that doesn't show up
statically in this file are goal, querying goal types, and automatically
casing. we'll use all of them pretty much constantly.

this is a perfectly adequate definition, but it's a bit tiresome for a
couple of reasons:

  - we have to prefix pretty much everything

  - we have to carry around the type variable A everywhere and we never do
    anything with it

we can fix the first complaint by using Agda's notion of _mixfix_
identifiers: whenever `_` appears in any identifier, it stands for the next
curried argument read in left to right order. so we can rewrite the type of
lists as

```agda
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A
```

to indicate that we intend to use `::` in between its two arguments. this
isn't just infixing; you can have as many `_` as you want and they can
start the identifier to get you post-fix notation.

using this type, we can rewrite append in a more familiar shape

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

we can use the mixfix mechanism for any identifier, too, not just in types
or type constructor names:

```agda
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)
```

identity type
-------------

before we can prove anything interesting, we need a notion of identity, so
that we can even begin to state things like "x is y". there is a whole lot
of interesting discussion about what this should be and why. let's not
worry about it. this is a perfectly good definition for us.

there's some technical junk going on here, about levels, that you don't
need to worry about. i'm including it because it lets us associate our
definition with agda's built in equals, with that `{-# BUILTIN ... #-}`
junk, which is convenient.

```agda
  open import Agda.Primitive using (Level; lzero; lsuc)

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
     refl : M == M
  infixr 9 _==_

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL refl #-}
```

because the introduces identities as just another type family, we can
compute on them pretty much like normal and show that they have the
properties we'd expect.

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
tool for swapping out an expression for one to which it's identified.

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
just hammer through the cases.

this is sometimes great, and sometimes it means that you do a lot more work
than you really need to and end up producing something hard to read. in
this case, note that we do fundimentally the same thing in the latter four
cases: we note that you can swap equals for equals in the second argument
of a `::` and then recurr on `a` with the other lists unchanged.

a tighter proof, then, only matches on `a` :

```agda
  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] b c = refl
  ++assoc (a :: as) b c = ap (_::_ a) (++assoc as b c)
```

the problem here, at least for my money, is that this makes a ton of sense
dynamically while we're writing it, but i have a really hard time looking
back at it and remembering how the proof went.

the solution to this complaint is a beautiful use of mix fix notation: we
can define a notation for linking together a bunch of appeals to
transitivity that lets us write the end points of each step explicitly in
the program text, even when agda doesn't need them:

```agda
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

this also lets us get a handle on exactly when agda wants to reduce
expressions. it's a little inconsistent with this, and sometimes will
reduce things beyond the point where you had a lemma that you wanted to
apply. this can make the type that appears in the goal seem impossible to
fulfill, because agda's busily doing its best impression of a freshman and
just applying evaluation rules whenever it feels like it.


foldr and foldl
---------------

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

which abstract the patterns of structural and tail recursion, respectively.

RANT ABOUT ELIPSIS DOTS GOES HERE

instead of the handwavey explanation that we get in the SML basis library
and almost every functional programming text book, let's really dive into
how these things relate to one another.

specifically, the intuition is that if `f` has some property, they should
produce the same answer. so that is to say that under some condition, we
should be able to write a program at type

```agda
  foldlr : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                {! something about f !} →
                foldr f b L == foldl f b L
```

the normal thing to say is that `f` is associative, commutative, and that
`b` is a unit for it. this doesn't actually make a lot of sense, and is
kind of a pet peeve of mine: all three things are really normally only
defined on `A x A -> A`, so it's not really clear what that means. the weak
answer is to restrict `f` to a lower type, but then we're not really
working with the functions as given.

we can do better!

so let's think of a property for `f` that does make sense with respect to
its real type. there's kind of only one thing that you can do that has a
"move the arguments around!" kind of flavor to it and still type checks:

```agda
  f a (f b c) == f b (f a c)
```

it's easy to check that if `A` and `B` are the same and `f` is commutative
and associative then it also has this property, so that's a sign that we're
on the right track. (there's also nothing else that type checks)

restating our theorem, we get

```agda
  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (L : List A)
                (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                foldr f b L == foldl f b L
```

naming the proof term of this property Δ. (if you know a better name:
please tell me.)

so let follow our noses and try to prove it! we have a list, surely we can
induct on that.

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

the type of that unfilled hole is

```agda
  f x (foldl f b L) == foldl f (f x b) L
```

which doesn't even look true. there isn't much else we could have done
while still following our noses and the shape of the types invovled, so
this is pretty much a dead end. we need to be clever.
