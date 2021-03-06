module foldrl-simpler where
  -- the familiar inductive definition of a list. only difference is that
  -- we need to explicitly list variables over which the definition is
  -- polymorphic
  data List0 (A : Set) : Set where
    [] : List0 A
    ::0 : A → List0 A → List0 A

  -- this is fine, but not quite the best definition because it requires
  -- that we prefix all the applications of ::, which gets really old
  -- really fast. so for example if we wrote append with this definition,
  -- it would look like this:

  -- META (introduce holes and casing here)
  ++0 : (A : Set) → List0 A → List0 A → List0 A
  ++0 A [] l2 = l2
  ++0 A (::0 x l1) l2 = ::0 x (++0 A l1 l2)

  -- to change that, we use agda's notion of mixfix
  -- identifiers:

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  -- with this definition, we can write a more familiar append:

  -- META (reinforce holes and casing here)
  ++1 : (A : Set) → List A → List A → List A
  ++1 A [] l2 = l2
  ++1 A (x :: l1) l2 = x :: (++1 A l1 l2)

  -- this also ends up being a bit of a mouthful, because we have to carry
  -- around the type argument A all over the place but it never
  -- changes. agda doesn't offer SML-style type inference, but it has a
  -- mechanism for implicit arguments that lets you recover the kind of
  -- code you'd like to write in many cases, including this very simple
  -- case where A is an argument (that happens to stand for a type) that is
  -- never really used.
  ++2 : {A : Set} → List A → List A → List A
  ++2 [] l2 = l2
  ++2 (x :: l1) l2 = x :: (++2 l1 l2)


  -- the last improvement we'll make to append is that we can use the
  -- mix-fix feature of the langauge to make this look even more like the
  -- traditional append:
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)


  -- ok! let's prove something about just what we've got so far. to do
  -- that, we're going to need some notion of identity. this is an
  -- interesting question! here's one answer

  -- ignore this mostly
  open import Agda.Primitive using (Level; lzero; lsuc)

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
     refl : M == M
  infixr 9 _==_

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL refl #-}

  -- there's a bit of syntactic nonsense here to get it to play nice with
  -- agda's builtins, and therefore pattern matching, but it's pretty much
  -- what you would think.

  -- since idenities are just another type, we can write functions on them
  -- like we did lists. this shows that indentity is transitive:
  _·_ : {α : Set} {x y z : α} → x == y → y == z → x == z
  refl · refl = refl

  --- .. and symmetric
  ! : {α : Set} {x y : α} → x == y → y == x
  ! refl = refl

  -- (reflexivity is the defining characteristic, so it's self-evident)

  -- this is a slightly more interesting property of equality: we show that
  -- everything else that we define must respect it:
  ap : {α β : Set} {x y : α} (F : α → β)
          → x == y → F x == F y
  ap F refl = refl

  -- there's a lot more interesting stuff to talk about with
  -- identifications, but this is all we need to prove some theorems in Set
  -- today, so that's all i want to talk about.

  -- the most intersting theorem we can prove with what we have so far is
  -- that ++ is aassociative:

  -- (META: ask what to induct on, show brute force thing)
  ++assoc-1 : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc-1 [] [] [] = refl
  ++assoc-1 [] [] (x :: c) = refl
  ++assoc-1 [] (x :: b) [] = refl
  ++assoc-1 [] (x :: b) (x₁ :: c) = refl
  ++assoc-1 (x :: a) [] [] = ap (_::_ x) (++assoc-1 a [] [])
  ++assoc-1 (x :: a) [] (x₁ :: c) = ap (_::_ x) (++assoc-1 a [] (x₁ :: c))
  ++assoc-1 (x :: a) (x₁ :: b) [] = ap (_::_ x) (++assoc-1 a (x₁ :: b) [])
  ++assoc-1 (x :: a) (x₁ :: b) (x₂ :: c) = ap (_::_ x) (++assoc-1 a (x₁ :: b) (x₂ :: c))

  ++assoc0 : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc0 [] b c = refl
  ++assoc0 (a :: as) b c = ap (_::_ a) (++assoc0 as b c)

  -- ok so that's technically a proof of the theorem that we wanted, and i
  -- don't know about you, but i have no idea why now that i've filled all
  -- the holes. it's not really that readable. there's a very elegant use
  -- of mixfix that lets us address this, however, by naming the end points
  -- of a bunch of points in a chain of transitivities.
  infix  2 _■
  infixr 2 _=<_>_

  -- notation for proofs by transivity that allows us to explicitly name
  -- the end points
  _=<_>_ : {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
  _ =< p1 > p2 = p1 · p2

  -- postfix refl syntax; pairs well with above.
  _■ : {A : Set} (x : A) → x == x
  _■ _ = refl

  -- ok let's see how this goes (notice that agda does a bunch of
  -- normalization that's hard to control or understand always)
  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] b c = refl
  ++assoc (a :: as) b c with ++assoc as b c
  ... | ih = ((a :: as) ++ b) ++ c    =< refl >
              (a :: (as ++ b)) ++ c   =< ap (λ x → a :: x) ih >
               a :: (as ++ (b ++ c))  =< refl >
              (a :: as) ++ (b ++ c)   ■

  -- that ih thing is just a habit of mine; if i'm recurring on something
  -- structurally i use it to remind myself of what the right thing to
  -- assume is. totally not part of the language. the `with` construct is a
  -- lot more powerful than just letting me make short names for things.

  -- this is the higher order function that encapsulates structural
  -- recursion on lists
  foldr : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldr f b [] = b
  foldr f b (x :: l) = f x (foldr f b l)

  -- this is the higher order function that encapsulates tail recursion on
  -- lists
  foldl : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldl f b [] = b
  foldl f b (x :: l) = foldl f (f x b) l

  -- foldl commutes inside an application of f, if f has the right
  -- property. lemma for main claim below.
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

  -- mildly unreadable version, to show why =< ? > is worth the hassle
  foldl-comm-ur : {A B : Set} (f : A → B → B) (x : A) (b : B) (L : List A)
                      (Δ : (a b : A) (c : B) → f a (f b c) == f b (f a c) ) →
                      f x (foldl f b L) == foldl f (f x b) L
  foldl-comm-ur f x b [] Δ = refl
  foldl-comm-ur f x b (y :: L) Δ = ap (f x) (! (foldl-comm f y b L Δ))
                                 · (Δ x y (foldl f b L)
                                    · (ap (f y) (foldl-comm f x b L Δ)
                                         · foldl-comm f y (f x b) L Δ))

  -- main claim
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

  -- this shows that the Δ property really is a fair generalization /
  -- reckoning of the bizarre thing people usually say
  assoc-comm-Δ : {A : Set}
                 (_⊕_ : A → A → A)
                 (assoc : (a b c : A) → ((a ⊕ b) ⊕ c) == (a ⊕ (b ⊕ c)))
                 (comm : (a b : A) → (a ⊕ b) == (b ⊕ a)) →
                 ((a b c : A) →  (a ⊕ (b ⊕ c)) == (b ⊕ (a ⊕ c)))
  assoc-comm-Δ _⊕_ A C a b c = a ⊕ (b ⊕ c)    =< ! (A a b c) >
                               (a ⊕ b) ⊕ c    =< ap (λ x → x ⊕ c) (C a b) >
                               (b ⊕ a) ⊕ c    =< A b a c >
                               b ⊕ (a ⊕ c)    ■
