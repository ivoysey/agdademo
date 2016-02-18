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


structural editing
------------------

actual tutorial
===============

alright, let's get cracking!

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
