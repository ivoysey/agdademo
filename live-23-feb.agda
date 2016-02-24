module live-23-feb where

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)

  open import Agda.Primitive using (Level; lzero; lsuc)

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
     refl : M == M
  infixr 9 _==_

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL refl #-}

  ! : {A : Set} {x y : A} → x == y → y == x
  ! refl = refl

  _·_ : {A : Set} {x y z : A} → x == y → y == z → x == z
  refl · refl = refl

  ap : {A B : Set} {x y : A} (F : A → B) → x == y → F x == F y
  ap F refl = refl

  ++assoc : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc [] b c = refl
  ++assoc (x :: a) b c = ap (_::_ x) (++assoc a b c)

  infix  2 _■
  infixr 2 _=<_>_

  -- notation for proofs by transivity that allows us to explicitly name
  -- the end points
  _=<_>_ : {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
  _ =< p1 > p2 = p1 · p2

  -- postfix refl syntax; pairs well with above.
  _■ : {A : Set} (x : A) → x == x
  _■ _ = refl

  ++assoc' : {A : Set} → (a b c : List A) → ((a ++ b) ++ c) == (a ++ (b ++ c))
  ++assoc' [] b c = refl
  ++assoc' (x :: a) b c with ++assoc' a b c
  ... | ih = ((x :: a) ++ b) ++ c =< refl >
                          (x :: (a ++ b)) ++ c =< refl >
                          x :: ((a ++ b) ++ c) =< ap (_::_ x) ih >
                          x :: (a ++ (b ++ c)) =< refl >
                          (x :: a) ++ (b ++ c) ■

  foldr : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldr f b [] = b
  foldr f b (x :: l) = f x (foldr f b l)

  foldl : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldl f b [] = b
  foldl f b (x :: l) = foldl f (f x b) l


  fold-comm : {A B : Set} (f : A → B → B) (x : A) (b : B) (l : List A)
                (Δ : (a b : A) (c : B) → (f a (f b c)) == (f b (f a c))) →
        f x (foldl f b l) == foldl f (f x b) l
  fold-comm f x b [] Δ = refl
  fold-comm f x b (y :: l) Δ with fold-comm f x b l Δ
  ... | ih = f x (foldl f b (y :: l)) =< refl >
             f x (foldl f (f y b) l) =< ap (f x) (! (fold-comm f y b l Δ)) >
             f x (f y (foldl f b l)) =< Δ x y (foldl f b l) >
             f y (f x (foldl f b l)) =< ap (f y) ih >
             f y (foldl f (f x b) l) =< fold-comm f y (f x b) l Δ >
             foldl f (f y (f x b)) l =< refl >
             foldl f (f x b) (y :: l) ■

  foldlrΔ : {A B : Set} (f : A → B → B) (b : B) (l : List A)
                   (Δ : (a b : A) (c : B) → (f a (f b c)) == (f b (f a c))) →
                   (foldr f b l) == (foldl f b l)
  foldlrΔ f b [] Δ = refl
  foldlrΔ f b (x :: l) Δ with foldlrΔ f b l Δ
  ... | ih = foldr f b (x :: l) =< refl >
             f x (foldr f b l)  =< ap (f x) ih >
             f x (foldl f b l)  =< fold-comm f x b l Δ >
             foldl f (f x b) l  =< refl >
             foldl f b (x :: l) ■
