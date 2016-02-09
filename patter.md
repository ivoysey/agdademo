intro
=====

hi!

for the couple of people in here that don't know me, i'm ian voysey. today
i'm going to give you a taste of what it's like to use agda to prove some
theorems about functional programs.

you can find the source for everything i'm doing (and most of the words
that i'm saying right now) on my github at http://github.com/ivoysey/agdademo

there's two things that i'm specifically _not_ going to do, so let's get
that out of the way:

  - there's a lot of really interesting work happening right now using agda
    to formalize some of the developments in HoTT. i'm not going to talk
    about that at all.

    if the technical details mean something, i'm not going to stay entirely
    inside set so there's nothing higher order happening here even though
    most of it probably works in that more general setting.

    i think it's better to have a really good understanding of agda as a
    tool before trying to use it to think about HoTT as a domain. doing so
    requires that you use some of the more arcane features of the language,
    and it's really exciting, but not a great place to start.

    for more information about that, talk to me later or talk to the
    experts: favonia, evan cavallo, ed morehouse, carlo, and dan licata.

  - i'm also not going to start at the very beginning. there's another file
    that i have in the background with some lemmas that are pretty pedantic
    and not a good introduction to the language, if you want all the gorey
    details. there's also a bunch of really great tutorials on the internet
    that will help you learn for that addition on naturals is commutative,
    etc., and i'm going to elide a bunch of that.

    a really great resource to start with from here is dan licata's agda
    course from Wesleyan. he's offered access to anyone at cmu that wants
    to see the materials if you shoot him an email at drl@cs.cmu.edu.

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

actual example
==============

alright, let's get cracking!

it's easy to define types in agda; here's the familiar type of lists.

on that type we can write functions pretty much as normal, via pattern
matching as given by the data type declaration. for example, here's the
standard structurally recursive append function for lists:

three things to note here:

  - agda supports a generalization of pre- and postfix operatiors called
    _mixfix_. if an `_` appears in an identifier at function type, it
    stands in the place of the next argument as given by a left-to-right
    reading of the type.

  - one of my favorite features of agda is a _hole_. you can put a `?` in
    the text of your program pretty much wherever you don't feel like
    writing a sub-expression and come back to it later.

  - second, you'll notice that i didn't do a lot of typing as i wrote that
    out! this is the pay off for having a structured editing
    environment. the emacs mode knows a ton about what's happening in the
    program and the types defined so far, so emacs and agda will
    collaborate to generate exhaustive cases for you when you press `C-c
    C-c` in a hole.
