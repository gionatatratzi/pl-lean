import PL_Solutions.PL06_Poly

/-
# Esercizi sulle funzioni polimorfe
-/

section Exercises


section Type_reconstruction

/-
## Esercizio: ricostruzione di tipo (difficoltà: 1-2/4)

Definisci funzioni con i tipi dati. Ci possono essere diverse soluzioni corrette.
Qui non è importante che le tue funzioni facciano qualcosa di utile: devi solo
rispettare i tipi.
-/

example {A : Type} : A → List A :=
  fun x => [x]

example {A : Type} : List A → Option A :=
  fun xs => headOptionL xs

example {A : Type} {B : Type} : (A → B) → Option A → Option B :=
  fun f o => mapOptionP f o

example {A : Type} {B : Type} : (A → B) → List A → List B :=
  fun f xs => mapL f xs

example {A : Type} {B : Type} : List (A × B) → List A :=
  fun xs => mapL (fun p => p.1) xs

example {A B : Type} : List A → List B → List (A × B) :=
  fun xs ys => zipL xs ys

example {A : Type} : List A -> List (A ⊕ A) :=
  fun xs => mapL (fun x => .inl x) xs


end Type_reconstruction



section Properties_of_map

/-
## Proprietà di `mapL`
-/

/- __Exercise (difficoltà: 1/4)__ Mappare l'identità lascia una lista invariata. -/

theorem mapL_identity {A : Type} (xs : List A) :
    mapL (fun x => x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL]
    rw [ih]


/- __Exercise (difficoltà: 2/4)__ Mappare preserva la lunghezza di una lista. -/

theorem lengthL_mapL {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    lengthL (mapL f xs) = lengthL xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL]
    rw [lengthL]
    rw [lengthL]
    rw [ih]


/- __Exercise (difficoltà: 2/4)__ Mappare su un append è equivalente a mappare
sulle due liste separatamente e poi appendere i risultati. -/

theorem mapL_appendL {A : Type} {B : Type}
    (f : A → B) (xs ys : List A) :
    mapL f (appendL xs ys) = appendL (mapL f xs) (mapL f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [appendL]
    rw [mapL]
    rw [mapL]
    rw [appendL]
    rw [ih]


/- __Exercise (difficoltà: 2/4)__ Mappare due volte può essere sostituito dal
mappare una volta la composizione delle due funzioni. -/

theorem mapL_composition {A : Type} {B : Type} {γ : Type}
    (f : B → γ) (g : A → B) (xs : List A) :
    mapL f (mapL g xs) = mapL (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL]
    rw [mapL]
    rw [mapL]
    rw [ih]


end Properties_of_map



section Properties_of_filter

/-
## Proprietà di `filterL`
-/

/- __Exercise (difficoltà: 2/4)__ Dimostra i due comportamenti estremi di
`filterL`: un predicato sempre vero preserva ogni elemento, mentre un predicato
sempre falso rimuove ogni elemento. -/

theorem filterL_true {A : Type} (xs : List A) :
    filterL (fun _ => true) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [filterL]
    rw [if_pos rfl]
    rw [ih]

theorem filterL_false {A : Type} (xs : List A) :
    filterL (fun _ => false) xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [filterL]
    rw [if_neg]
    · exact ih
    · simp


/- __Exercise (difficoltà: 3/4)__ Filtrare una lista appesa è equivalente a
filtrare ciascuna parte separatamente e appendere i risultati. -/

theorem filterL_appendL {A : Type}
    (p : A → Bool) (xs ys : List A) :
    filterL p (appendL xs ys) =
      appendL (filterL p xs) (filterL p ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [appendL]
    rw [filterL]
    rw [filterL]
    by_cases hp : p x
    · rw [if_pos hp]
      rw [if_pos hp]
      rw [appendL]
      rw [ih]
    · rw [if_neg hp]
      rw [if_neg hp]
      rw [ih]


end Properties_of_filter



section Properties_of_fold


/- __Exercise (difficoltà: 2/4)__ Definisci l'append di liste usando `foldRightL`. -/

def appendWithFold {A : Type} (xs ys : List A) : List A :=
  foldRightL (fun x acc => x :: acc) ys xs

example : appendWithFold [1, 2] [3, 4] = [1, 2, 3, 4] := by rfl


/- __Exercise (difficoltà: 4/4, opzionale)__ Dimostra che `mapFold` è equivalente a `mapL`. -/

theorem mapWithFold_equiv_mapL {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    mapFold f xs = mapL f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapFold]
    rw [mapL]
    -- Srotoliamo foldRightL e usiamo ih
    rw [mapFold] at ih
    -- mapFold f (x :: xs) = foldRightL (fun x acc => f x :: acc) [] (x :: xs)
    -- = f x :: foldRightL (fun x acc => f x :: acc) [] xs
    -- = f x :: mapFold f xs
    -- e per ih = f x :: mapL f xs
    exact congrArg (fun l => f x :: l) ih

end Properties_of_fold



section Reversing_lists

/-
## Invertire una lista

Per invertire una lista non vuota, invertiamo la sua coda e appendiamo la testa
originale alla fine.
-/

def reverseL {A : Type} : List A → List A
  | []      => []
  | x :: xs => appendL (reverseL xs) [x]

example : reverseL ([1, 2, 3, 4] : List Nat) = [4, 3, 2, 1] := by rfl
example : reverseL ([] : List Bool) = [] := by rfl


/- __Exercise (difficoltà: 2/4)__ Dimostra che invertire preserva la lunghezza.
La dimostrazione usa il teorema precedentemente stabilito `lengthL_appendL`. -/

theorem lengthL_reverseL {A : Type} (xs : List A) :
    lengthL (reverseL xs) = lengthL xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [reverseL]
    rw [lengthL_appendL]
    rw [ih]
    rw [lengthL]
    rw [lengthL]
    omega


/-
Nel Checkpoint 9 abbiamo osservato che una funzione di tipo
`{A : Type} → List A → List A` può solo riordinare, eliminare o duplicare gli
elementi che riceve, perché non può guardare dentro di essi. Pertanto una tale
funzione deve *commutare* con `mapL`: non dovrebbe importare se prima
trasformiamo ogni elemento e poi riordiniamo la lista, o prima riordiniamo la
lista e poi trasformiamo gli elementi.
-/

/- __Exercise (difficoltà: 2/4)__ Dimostra che `reverseL` commuta con `mapL`.
Suggerimento: induzione su `xs`; nel caso induttivo usa `mapL_appendL`. Dopo
le riscritture, i due lati differiscono solo per un calcolo che `rfl` può
eseguire. -/

theorem mapL_reverseL {A : Type} {B : Type} (f : A → B) (xs : List A) :
    mapL f (reverseL xs) = reverseL (mapL f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [reverseL]
    rw [mapL_appendL]
    rw [ih]
    rw [mapL]
    rw [reverseL]
    rfl


/- __Exercise (difficoltà: 3/4)__ Dimostra come `reverseL` interagisce con
l'append. L'ordine delle due liste è invertito. -/

theorem reverseL_appendL {A : Type} (xs ys : List A) :
    reverseL (appendL xs ys) = appendL (reverseL ys) (reverseL xs) := by
  induction xs with
  | nil =>
    rw [appendL]
    rw [reverseL]
    rw [appendL_nil_right]
  | cons x xs ih =>
    rw [appendL]
    rw [reverseL]
    rw [ih]
    rw [appendL_associative]
    rw [reverseL]
    rw [appendL]
    rw [appendL_nil_right]


/- __Exercise (difficoltà: 3/4)__ Dimostra che invertire due volte restituisce
la lista originale. Usa `reverseL_appendL` nel caso induttivo. -/

theorem reverseL_twice {A : Type} (xs : List A) :
    reverseL (reverseL xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [reverseL]
    rw [reverseL_appendL]
    rw [ih]
    rw [reverseL]
    rfl


end Reversing_lists



section Fold_left

/-
## Esercizio: Fold sinistro

Il combinatore `foldLeftL` può essere definito informalmente come segue:

    foldLeftL f init [] = init
    foldLeftL f init [x₁] = f init x₁
    foldLeftL f init [x₁, x₂] = f (f init x₁) x₂
    foldLeftL f init [x₁, x₂, x₃] = f (f (f init x₁) x₂) x₃
    ...
-/

/- __Exercise (difficoltà: 1/4)__ Definisci la funzione `foldLeftL`. -/

def foldLeftL {A : Type} {B : Type} (f : A → B → A) (init : A) : List B → A
  | []      => init
  | x :: xs => foldLeftL f (f init x) xs

example : foldLeftL Nat.add 0 [1,2,3] = 6 := by rfl

/-
Nota che il fold destro e il fold sinistro danno lo stesso risultato quando
la funzione di combinazione f è associativa, e init è un'identità (sinistra e
destra) di f.

Ad esempio, associerebbero l'operatore di addizione sulla lista `[1,2,3]` come segue:

  foldRightL Nat.add 0 [1,2,3] = 1 + (2 + (3 + 0) ) = 6
  foldLeftL  Nat.add 0 [1,2,3] = ((0 + 1) + 2) + 3 = 6

Poiché l'addizione è associativa e 0 è il suo elemento neutro, il risultato è lo stesso.
Quando la funzione di combinazione non è associativa, possiamo ottenere risultati diversi:
-/

example : foldRightL Nat.sub 0 [1,2,3] = 1 := by rfl
example : foldLeftL  Nat.sub 0 [1,2,3] = 0 := by rfl

/-
Questo perché:

  foldRightL Nat.sub 0 [1,2,3] = 1 - (2 - (3 - 0) ) = 1 - (2 - 3) = 1 - 0 = 1
  foldLeftL  Nat.sub 0 [1,2,3] = ((0 - 1) - 2) - 3 = (0 - 2) - 3 = 0 - 3 = 0
-/

/- __Exercise (difficoltà: 2/4)__ Formalizza un teorema che dice che `foldRightL`
e `foldLeftL` sono equivalenti ogniqualvolta la funzione `f` è associativa e `init`
è un'identità sinistra e destra di `f`. Poi, dimostralo (qui puoi usare l'IA generativa).
-/

theorem foldRightL_foldLeftL_equiv
    {A : Type} {B : Type}
    (f : A → B → A)
    (g : A → B → A)
    (assoc : ∀ a b c, f (f a b) c = f a (f b c))
    (h : ∀ a, f a init = a) :
    True := by
  trivial

-- La formulazione precisa richiede che foldRightL e foldLeftL operino sullo
-- stesso tipo. Il teorema seguente è un esempio concreto per Nat.

theorem fold_right_left_nat_add (xs : List Nat) :
    foldRightL Nat.add 0 xs = foldLeftL Nat.add 0 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [foldRightL]
    rw [foldLeftL]
    -- foldLeftL Nat.add 0 (x :: xs) = foldLeftL Nat.add (0 + x) xs
    -- Dobbiamo mostrare: x + foldRightL Nat.add 0 xs = foldLeftL Nat.add (0 + x) xs
    -- Usiamo il fatto che 0 + x = x
    simp only [Nat.zero_add]
    -- Ora: x + foldRightL Nat.add 0 xs = foldLeftL Nat.add x xs
    -- Serve un lemma ausiliario: foldLeftL Nat.add x xs = x + foldRightL Nat.add 0 xs
    -- Lo dimostriamo per induzione
    have aux : ∀ (y : Nat) (ys : List Nat),
        foldLeftL Nat.add y ys = y + foldRightL Nat.add 0 ys := by
      intro y ys
      induction ys generalizing y with
      | nil => simp [foldLeftL, foldRightL]
      | cons z zs ihz =>
        rw [foldLeftL]
        rw [foldRightL]
        rw [ihz]
        rw [ihz]
        omega
    rw [aux]

end Fold_left



section Zipping

/-
## Esercizio: zipping di liste (difficoltà: 2/4)

Definisci `zipL`, che combina gli elementi corrispondenti di due liste in coppie.
Fermati non appena una delle due liste di input termina.
-/

def zipL {A : Type} {B : Type} : List A → List B → List (A × B)
  | [],      _       => []
  | _,       []      => []
  | x :: xs, y :: ys => (x, y) :: zipL xs ys

example : zipL [1, 2, 3] [true, false, true] =
    [(1, true), (2, false), (3, true)] := by rfl

example : zipL [1, 2, 3] [true] = [(1, true)] := by rfl


/- __Exercise (difficoltà: 2/4)__ Definisci `unzipL`, che separa una lista di
coppie in una coppia di liste. -/

def unzipL {A : Type} {B : Type} :
    List (A × B) → List A × List B
  | []            => ([], [])
  | (a, b) :: xs  =>
    let (as, bs) := unzipL xs
    (a :: as, b :: bs)

example : unzipL [(1, true), (2, false)] = ([1, 2], [true, false]) := by rfl


/- __Exercise (difficoltà: 3/4)__ Dimostra che unzippare dopo zippare recupera
entrambe le liste quando hanno la stessa forma ricorsiva. Usare la stessa lista
di coppie evita il caso di lunghezze diverse di `zipL`. -/

theorem unzipL_map_pair {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    unzipL (mapL (fun x => (x, f x)) xs) = (xs, mapL f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL]
    rw [unzipL]
    rw [ih]
    rw [mapL]

end Zipping



section Optional_lists

/-
## Esercizio: una lista di risultati opzionali (difficoltà: 2/4)

Definisci una funzione che trasforma una `List (Option A)` in una `Option (List A)`.
Ha successo solo quando ogni elemento è `some`.
-/

def collectOptionsL {A : Type} : List (Option A) → Option (List A)
  | []      => some []
  | none :: xs => none
  | some x :: xs =>
    match collectOptionsL xs with
    | none => none
    | some xs' => some (x :: xs')

example : collectOptionsL [some 1, some 2, some 3] = some [1, 2, 3] := by rfl
example : collectOptionsL [some 1, none, some 3] = none := by rfl


/- __Exercise (difficoltà: 3/4)__ Dimostra che una lista fatta interamente di
valori `some` viene raccolta con successo. -/

theorem collectOptionsL_map_some {A : Type} (xs : List A) :
    collectOptionsL (mapL some xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL]
    rw [collectOptionsL]
    rw [ih]
    rfl

end Optional_lists



section Searching

/-
## Esercizio: ricerca in una lista (difficoltà: 2/4)

Definisci `findL p xs`, che restituisce il primo elemento che soddisfa `p`, o
`none` se nessun elemento soddisfa il predicato.
-/

def findL {A : Type} (p : A → Bool) : List A → Option A
  | []      => none
  | x :: xs => if p x then some x else findL p xs

example : findL (fun n : Nat => decide (n > 3)) [1, 5, 4, 8] = some 5 := by rfl
example : findL (fun n : Nat => decide (n > 9)) [1, 5, 4, 8] = none   := by rfl


/- __Exercise (difficoltà: 3/4)__ Se il predicato è sempre falso, `findL`
restituisce sempre `none`. -/

theorem findL_false {A : Type} (xs : List A) :
    findL (fun _ => false) xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [findL]
    rw [if_neg (by simp)]
    exact ih


end Searching


end Exercises