module foldrl where
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)


  foldr : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldr f b [] = b
  foldr f b (x :: l) = f x (foldr f b l)

  foldl : {A B : Set} (f : A → B → B) (b : B) (l : List A) → B
  foldl f b [] = b
  foldl f b (x :: l) = foldl f (f x b) l
