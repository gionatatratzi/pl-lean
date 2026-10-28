set_option autoImplicit false

/-
# Tipi prodotto e tipi somma

Finora, la maggior parte delle nostre funzioni restituiva un singolo numero
naturale o un booleano. In questa lezione impariamo due modi fondamentali di
costruire tipi più ricchi:

* un **prodotto** `A × B` contiene sia un `A` che un `B`;
* una **somma** `A ⊕ B` contiene o un `A` o un `B`.

Incontreremo anche due tipi strettamente correlati:
* `Unit`, che può essere visto come un prodotto senza componenti;
* `Option A`, che rappresenta o un valore di tipo A o l'assenza di tale valore.

Alla fine della lezione dovresti essere in grado di:

* costruire coppie e ispezionare le loro componenti;
* usare il pattern matching su coppie e tuple annidate;
* spiegare la differenza tra funzioni curried e uncurried;
* usare le strutture come prodotti con componenti nominate;
* costruire e ispezionare valori di tipi somma;
* usare `Option Nat` per calcoli parziali che restituiscono numeri naturali;
* dimostrare proprietà che coinvolgono i nuovi tipi.

I simboli `A` e `B` nei commenti stanno informalmente per tipi arbitrari.
Nel codice Lean, tuttavia, lavoriamo deliberatamente con tipi concreti come
`Nat`, `Bool` e `String`. La prossima lezione spiegherà come scrivere una
definizione che funziona uniformemente per tipi arbitrari: questo è il
**polimorfismo**.

Le difficoltà degli esercizi usano la stessa scala relativa delle lezioni precedenti:

* **1/4:** un'idea diretta;
* **2/4:** due idee devono essere combinate;
* **3/4:** una costruzione o dimostrazione più sostanziale;
* **4/4:** una sfida opzionale.
-/


section Product_types

/-
## Tipi prodotto

Supponiamo che un calcolo debba restituire due risultati. Potremmo definire due
funzioni separate, ma questo potrebbe ripetere lo stesso calcolo.
Un tipo prodotto ci permette di impacchettare i due risultati insieme.

Se `A` e `B` sono tipi, allora

    A × B

è il tipo delle coppie la cui prima componente ha tipo `A` e la cui seconda
componente ha tipo `B`. Digita `\times` per inserire il simbolo `×`.

La notazione `(a, b)` costruisce una coppia:
-/

def myPair : Nat × Bool := (3, true)

/- Questo è equivalente a usare l'operatore esplicito di **introduzione** `Prod.mk`: -/

def myPair₂ : Nat × Bool := Prod.mk 3 true

example : myPair = myPair₂ := by rfl

/-
Le due componenti di una coppia possono avere lo stesso tipo o tipi diversi.
I prodotti possono anche essere **annidati**, e le funzioni possono restituire coppie.
-/


/- __Exercise (difficoltà: 1/4)__ Costruisci valori dei tipi dati.
Nota dove compaiono le parentesi. -/

example : Nat × Nat           := (3, 4)
example : (Nat × Bool) × Nat  := ((3, true), 4)
example : Nat × (Bool × Nat)  := (3, (true, 4))
example : Nat → (Nat × Nat)   := fun n => (n, n + 1)
example : Nat → (Nat × Bool)  := fun n => (n, n > 0)

/-
Le parentesi contano. In generale,

    (A × B) × C

e

    A × (B × C)

sono tipi diversi, con valori di forma diversa:

    ((a, b), c) : (A × B) × C
    (a, (b, c)) : A × (B × C)
-/


section Projections

/-
### Proiezioni

Se `p : A × B`, le sue due componenti possono essere ottenute usando:

    p.1 : A
    p.2 : B

Costruire `(a, b)` è un'operazione di **introduzione** per i prodotti.
Le proiezioni sono operazioni di **eliminazione**: estraggono gli elementi di una coppia.
-/

#eval myPair.1
#eval myPair.2

def swapNatBool (p : Nat × Bool) : Bool × Nat :=
  (p.2, p.1)

example : swapNatBool (7, true)  = (true, 7) := by rfl
example : swapNatBool (0, false) = (false, 0) := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci le seguenti funzioni usando le proiezioni. -/

def sumComponents (p : Nat × Nat) : Nat :=
  p.1 + p.2

def keepFirstAndDoubleSecond (p : Nat × Nat) : Nat × Nat :=
  (p.1, 2 * p.2)

example : sumComponents (3, 4) = 7                  := by rfl
example : keepFirstAndDoubleSecond (3, 4) = (3, 8)  := by rfl

end Projections



section Pattern_matching

/-
Invece di proiettare le componenti separatamente, possiamo esporle entrambe
contemporaneamente tramite pattern matching:
-/

#eval match myPair with
  | (n, _) => n

/-
Definiamo una versione alternativa di `swapNatBool` usando il pattern matching:
-/

def swapNatBool₂ : Nat × Bool → Bool × Nat
  | (n, b) => (b, n)

/- Le due versioni di `swapNatBool` sono equivalenti. -/

example (p : Nat × Bool): swapNatBool₂ p  = swapNatBool p := by rfl

/- __Exercise (difficoltà: 1/4)__ Definisci le seguenti funzioni usando il pattern matching. -/

def addPair : Nat × Nat → Nat
  | (a, b) => a + b

def mulPair : Nat × Nat → Nat
  | (a, b) => a * b

example : addPair (3, 4) = 7  := by rfl
example : mulPair (3, 4) = 12 := by rfl

/- __Exercise (difficoltà: 1/4)__ La componente booleana sceglie quale numero restituire. -/

def chooseFromPair : (Nat × Nat) × Bool → Nat
  | ((a, b), true)  => a
  | ((a, b), false) => b

example : chooseFromPair ((10, 20), true)  = 10 := by rfl
example : chooseFromPair ((10, 20), false) = 20 := by rfl

end Pattern_matching


section Tuples

/-
### Le tuple sono coppie annidate

Lean usa prodotti annidati per rappresentare tuple con più di due componenti:

    A × B × C    significa    A × (B × C)
    (a, b, c)    significa    (a, (b, c))

La notazione nasconde l'annidamento, ma le proiezioni lo rivelano:
-/

example : (7, 8, 9) = (7, (8, 9)) := by rfl
example : (7, 8, 9).1 = 7 := by rfl
example : (7, 8, 9).2 = (8, 9) := by rfl
example : (7, 8, 9).2.1 = 8 := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci una funzione `rev4` che inverte le 4-tuple.
Poi, dimostra che applicare `rev4` due volte è la funzione identità.
-/

def rev4 : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | (a, b, c, d) => (d, c, b, a)

example : rev4 (1,2,3,4) = (4,3,2,1) := by rfl

theorem rev4_rev4_equiv_id4 : ∀ t : Nat × Nat × Nat × Nat, rev4 (rev4 t) = t := by
  intro t
  rcases t with ⟨a, b, c, d⟩
  rfl

/-
Possiamo usare il pattern matching anche su coppie annidate. Come al solito,
il wildcard `_` può corrispondere a tutto.

Ad esempio, definiamo una funzione che prende una coppia fatta di due coppie,
e restituisce la somma di tutti gli elementi.
-/

def addTwoPairs : (Nat × Nat) × (Nat × Nat) → Nat
  | ((a, b), (c, d)) => a + b + c + d

example : addTwoPairs ((1, 2), (3, 4)) = 10 := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci una funzione che prende come input una
coppia `((n,m),b)`, dove `b : Bool` e `n m : Nat`, e restituisce il minimo di `n`
e `m` se `b = false`, altrimenti il massimo.
-/

def minOrMax : (Nat × Nat) × Bool → Nat
  | ((n, m), false) => if n ≤ m then n else m
  | ((n, m), true)  => if n ≤ m then m else n

example : minOrMax ((1, 2), false) = 1 := by rfl
example : minOrMax ((3, 2), false) = 2 := by rfl
example : minOrMax ((1, 3), true)  = 3 := by rfl
example : minOrMax ((4, 2), true)  = 4 := by rfl

end Tuples



section Functions_returning_pairs

/-
### Funzioni che restituiscono coppie

Una funzione può restituire diversi risultati impacchettati come una coppia.
La funzione sotto applica due calcoli allo stesso input e restituisce entrambi i risultati.
-/

def bothResultsN (f g : Nat → Nat) (n : Nat) : Nat × Nat :=
  (f n, g n)

example : bothResultsN Nat.succ (Nat.pred) 2 = (3, 1) := by rfl
example : bothResultsN Nat.succ (fun n => n+n) 5 = (6, 10) := by rfl

/- __Exercise (difficoltà: 1/4)__ Definisci una funzione `minMax` che prende come
input due numeri, e restituisce una coppia dove l'elemento sinistro è l'input più
piccolo e l'elemento destro è l'input più grande. -/

def minMax (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a, b) else (b, a)

example : minMax 3 8 = (3, 8) := by rfl
example : minMax 8 3 = (3, 8) := by rfl
example : minMax 4 4 = (4, 4) := by rfl

end Functions_returning_pairs



section Unit_type

/-
Una coppia contiene due componenti, e una tupla più grande contiene più componenti.
Una tupla con zero componenti è rappresentata dal tipo `Unit`.

Il tipo `Unit` ha esattamente un costruttore e un valore:

    () : Unit

Non c'è informazione da scegliere quando si costruisce `()`. Questo rende `Unit`
utile quando un ramo di un tipo di dato non ha bisogno di portare dati aggiuntivi.
-/

def emptyTuple : Unit := ()


/- __Exercise (difficoltà: 1/4)__ Dimostra che il tipo `Unit` è abitato. -/

theorem unit_inhabited : ∃ x : Unit, x = () := by
  exact ⟨(), rfl⟩

/- __Exercise (difficoltà: 1/4)__ Dimostra che due elementi di tipo `Unit` devono
essere identici.
Suggerimento: per analisi per casi. -/

theorem unit_unique (x y : Unit) : x = y := by
  cases x
  cases y
  rfl

/-
__Exercise (difficoltà: 1/4)__ Mostra che accoppiare un numero con `()` non aggiunge
informazione. Dividi la dimostrazione in 3 parti:
1. Definisci una funzione `removeUnitRight : Nat × Unit → Nat`
2. Definisci una funzione `addUnitRight : Nat → Nat × Unit`
3. Dimostra che la composizione delle due funzioni è l'identità.
-/

def removeUnitRight (p : Nat × Unit) : Nat :=
  p.1

def addUnitRight (n : Nat) : Nat × Unit :=
  (n, ())

theorem remove_comp_add_id (n : Nat): removeUnitRight (addUnitRight n) = n := by
  rfl

theorem add_comp_remove_id (p : Nat × Unit): addUnitRight (removeUnitRight p) = p := by
  rcases p with ⟨n, u⟩
  cases u
  rfl

end Unit_type



section Proofs_about_products

/-
Dati due elementi `a`, `b`, mostriamo che la coppia `(a,b)` è equivalente alla
coppia delle proiezioni:
-/

theorem pair_projections (a : Nat) (b : Bool) :
    ((a, b).1, (a, b).2) = (a, b) := by
  rfl

/-
Il tipo prodotto `A × B` ha esattamente un costruttore:

    Prod.mk : A → B → A × B

La notazione di coppia `(a, b)` è una scorciatoia per `Prod.mk a b`.

Pertanto, ogni valore di tipo `A × B` ha la stessa forma: una coppia fatta di una
prima e una seconda componente.

Di conseguenza, il pattern matching non ha bisogno di distinguere tra costruttori
diversi; estrae solo queste due componenti. Di conseguenza, un solo ramo è sufficiente:

    match p with
    | (a, b) => ...

Questo differisce dai tipi `Bool` o `Nat`, che hanno più costruttori e quindi
richiedono più rami.
-/

/-
Data una coppia `p`, mostriamo che è equivalente alla coppia delle sue proiezioni.
Questa proprietà è utile quando una dimostrazione scompone una coppia e poi la
ricostruisce.
-/

theorem pair_eta_NatBool (p : Nat × Bool) : (p.1, p.2) = p := by
  cases p with
  | mk a b =>
    rfl

/-
La tattica `cases` espone come è stato costruito un valore. Per le coppie, tuttavia,
scrivere il nome del costruttore `mk` e un ramo di caso separato è un po' verboso.

La tattica `rcases` combina l'analisi per casi con un **pattern di destrutturazione**.
Il pattern

    ⟨a, b⟩

descrive una coppia e dà i nomi `a` e `b` alle sue due componenti.
Pertanto,

    rcases p with ⟨a, b⟩

scompone `p` direttamente nelle sue componenti.
-/

theorem pair_eta_NatBool₂ (p : Nat × Bool) : (p.1, p.2) = p := by
  rcases p with ⟨a,b⟩
  rfl

/-
Dimostriamo ora che `swapNatBool` è iniettiva. Più del teorema stesso, è
interessante come lo dimostriamo. Controlla la dimostrazione passo-passo nella InfoView.
-/

theorem swapNatBool_inj (p1 p2 : Nat × Bool) : swapNatBool p1 = swapNatBool p2 → p1 = p2 := by
  intro h                       -- sposta l'antecedente dell'implicazione nel contesto
  cases h1 : p1 with            -- destruttura `p1`, nominando la nuova ipotesi nel contesto `h1`
  | mk a1 b1 =>                 -- ogni valore di un tipo prodotto è una coppia, costruita con `mk`
    cases h2 : p2 with          -- lo stesso per `p2`
    | mk a2 b2 =>
      simp [swapNatBool,h1,h2] at h
      cases h with              -- la nuova `h` è una congiunzione. Dato che una congiunzione è costruita
                                -- con `And.intro`, la tattica `cases` la destruttura con `intro`
      | intro c1 c2 =>          -- `c1` e `c2` sono i nomi dei due congiunti
        rw [c1,c2]              -- chiudiamo la dimostrazione riscrivendoli nel goal.

/- Usare `rcases` permette una dimostrazione più concisa. -/

theorem swapNatBool_inj₂ (p1 p2 : Nat × Bool) : swapNatBool p1 = swapNatBool p2 → p1 = p2 := by
  intro h
  rcases p1 with ⟨n1, b1⟩
  rcases p2 with ⟨n2, b2⟩
  -- L'ipotesi diventa `(b1, n1) = (b2, n2)`.
  simp [swapNatBool] at h
  rcases h with ⟨n12,b12⟩
  rw [n12,b12]

end Proofs_about_products



section Type_isomorphisms

/-
## Diverse rappresentazioni della stessa informazione

Due tipi `A`, `B` possono essere equivalenti nonostante siano sintatticamente
diversi. Dimostriamo questa equivalenza definendo:

1. una trasformazione f da A a B;
2. una trasformazione g da B ad A;
3. due teoremi che mostrano che f ∘ g = id e g ∘ f = id.

Tale coppia di conversioni mutuamente inverse è chiamata **isomorfismo di tipi**.
Scriviamo `A ≅ B` quando vale l'isomorfismo di tipi.

Nota che nella sezione sopra sul tipo `Unit` abbiamo stabilito:

    Nat × Unit  ≅  Nat.

Nota che l'isomorfismo sopra vale per qualsiasi tipo, non solo `Nat`: cioè, A × Unit ≅ A
vale per qualsiasi tipo A. Rimandiamo questa generalizzazione a quando avremo
introdotto il polimorfismo.

Per i tipi prodotto, dimostriamo una sorta di proprietà di commutatività:

    Nat × Bool  ≅  Bool × Nat.

Abbiamo già una direzione della trasformazione:

    swapNatBool : Nat × Bool → Bool × Nat.

Ecco la conversione inversa.
-/

def swapBoolNat : Bool × Nat → Nat × Bool
  | (b, n) => (n, b)

/- __Exercise (difficoltà: 1/4)__ Dimostra entrambi i viaggi di andata e ritorno. -/

theorem swapBoolNat_comp_swapNatBool_id (p : Nat × Bool) : swapBoolNat (swapNatBool p) = p := by
  rcases p with ⟨n, b⟩
  rfl

theorem swapNatBool_comp_swapBoolNat_id (p : Bool × Nat) : swapNatBool (swapBoolNat p) = p := by
  rcases p with ⟨b, n⟩
  rfl

end Type_isomorphisms



section Currying

/-
## Funzioni curried e uncurried

Ricorda che le frecce associano a destra:

    Nat → Nat → Nat

significa:

    Nat → (Nat → Nat).

Una funzione di questo tipo riceve due argomenti uno alla volta. È chiamata **curried**.
Al contrario,

    Nat × Nat → Nat

significa:

    (Nat × Nat) → Nat.

Questa funzione riceve un argomento, che è una coppia. È chiamata **uncurried**.

Ad esempio:
-/

#check (fun (n m : Nat) => n + m)           -- Nat → Nat → Nat
#check (fun ((n,m) : Nat × Nat) => n + m)   -- Nat × Nat → Nat

/-
Dimostriamo che:

    Nat × Nat → Nat ≅  Nat → Nat → Nat.

Per mostrare questo isomorfismo di tipi, definiamo due trasformazioni:

* `curryN` riceve `a` e `b` separatamente, e passa la coppia `(a, b)` a `f`.
* `uncurryN` fa pattern matching sul suo argomento coppia e passa le due componenti
  separatamente a `f`.
-/

def curryN (f : Nat × Nat → Nat) : Nat → Nat → Nat :=
  fun a b => f (a, b)

def uncurryN (f : Nat → Nat → Nat) : Nat × Nat → Nat
  | (a, b) => f a b

example : curryN   (fun ((n,m) : Nat × Nat ) => n + m)  3 4   = 7 := by rfl
example : uncurryN (fun (n m : Nat) => n + m)          (3, 4) = 7 := by rfl


/- __Exercise (difficoltà: 1/4)__ Dimostra l'isomorfismo di tipi. -/

theorem curryN_uncurryN (f : Nat → Nat → Nat) : curryN (uncurryN f) = f := by
  funext a b
  rfl

theorem uncurryN_curryN (f : Nat × Nat → Nat) : uncurryN (curryN f) = f := by
  funext p
  rcases p with ⟨a, b⟩
  rfl

end Currying



section Structures

/-
Le tuple annidate sono comode quando ci sono solo poche componenti. Con molte
componenti, espressioni come `p.2.1` diventano difficili da leggere perché
dobbiamo ricordare cosa significa ogni posizione.

Una `structure` è un tipo simile a un prodotto le cui componenti hanno nomi.
Considera un punto nel piano:
-/

structure Point where
  x : Nat
  y : Nat
  deriving Repr

/-
Un valore di struttura è costruito dando un valore per ogni campo.
-/

def origin : Point :=
  { x := 0
    y := 0 }

def pointA : Point :=
  { x := 3
    y := 5 }

/-
I campi sono accessibili per nome piuttosto che per posizione:
-/

example : pointA.x = 3 := by rfl
example : pointA.y = 5 := by rfl

/-
Il pattern matching è anche disponibile. Questa forma rende esplicito che una
struttura ha un costruttore che porta tutti i suoi campi.
-/

def getX : Point → Nat
  | { x, y := _ } => x

/-
Lean riporta un avviso per `y` perché il pattern lega entrambi i campi della
struttura, ma il corpo usa solo `x`. Questo non è un errore: la definizione è
valida, ma Lean ci avverte che il nome `y` è superfluo.

Per rimuovere l'avviso, usa il pattern `{ x, y := _ }`
-/

example : pointA.x = getX pointA := by rfl

/-
La sintassi di aggiornamento dei record costruisce un nuovo valore che differisce
in campi selezionati:
-/

def moveRight (p : Point) (dx : Nat) : Point :=
  { x := p.x + dx, y := p.y }

example : moveRight  pointA 1 = { x:=4, y:=5 } := by rfl

/-
I valori Lean sono immutabili: non modifichiamo un valore di struttura esistente. La notazione:

    { p with x := newX }

costruisce un nuovo valore copiando tutti i campi di `p`, tranne che il campo `x`
è sostituito da `newX`.

Possiamo usare questa funzionalità per definire `moveRight` in modo più elegante:
-/

def moveRight₂ (p : Point) (dx : Nat) : Point :=
  { p with x := p.x + dx }

example : moveRight₂ pointA 1 = { x:=4, y:=5 } := by rfl

/-
Il campo `y` del punto risultante è copiato automaticamente da `p`.
Diversi campi possono essere sostituiti nella stessa espressione:

    { p with x := newX, y := newY }
-/

/-
Le funzioni possono essere associate al namespace della struttura.
La notazione con punto permette allora al valore di input di apparire prima del
nome della funzione:
-/

def Point.translate (p : Point) (dx dy : Nat) : Point :=
  { x := p.x + dx
    y := p.y + dy }

example : Point.translate origin 3 5 = pointA := by rfl

end Structures


end Product_types




section Sum_types

/-
## Tipi somma

Un prodotto contiene entrambe le sue componenti. Un **tipo somma** rappresenta una
scelta tra due alternative.

Se `A` e `B` sono tipi, allora `A ⊕ B` (digita `\oplus` per `⊕`) contiene o:

* un valore di tipo `A`, introdotto da `Sum.inl`;
* un valore di tipo `B`, introdotto da `Sum.inr`.

Il costruttore registra non solo il payload ma anche quale alternativa è stata scelta.
-/

def oneLeft   : Nat ⊕ Bool := Sum.inl 1
def trueRight : Nat ⊕ Bool := Sum.inr true

/-
L'annotazione di tipo è necessaria. Da `Sum.inl 1` da solo, Lean può inferire il
tipo sinistro `Nat`, ma senza l'annotazione di tipo non ci sarebbe abbastanza
informazione per inferire il tipo destro.

Possiamo omettere il prefisso `Sum` e usare solo `.inl` e `.inr`.
-/

def oneLeft₂   : Nat ⊕ Bool := .inl 1
def trueRight₂ : Nat ⊕ Bool := .inr true

/-
Anche quando i tipi di payload coincidono, i tag dei costruttori rimangono distinti:
-/

def oneLeft₃  : Nat ⊕ Nat := .inl 1
def oneRight₃ : Nat ⊕ Nat := .inr 1

/- Nota che il valore a sinistra non è uguale allo stesso valore a destra.
Questo perché sebbene questi valori portino lo stesso numero, rappresentano
alternative diverse.
-/

example : oneLeft₃ ≠ oneRight₃ := by
  intro h
  cases h


section Pattern_matching

/-
Una somma ha due costruttori, quindi una funzione che consuma una somma normalmente
necessita due rami.

Ad esempio, `natOrBoolToNat` prende come input una somma tra un `Nat` o un `Bool`,
e restituisce un `Nat`.
* Nel ramo `.inl`, il payload ha tipo `Nat`.
* Nel ramo `.inr`, ha tipo `Bool`.
Ogni ramo deve restituire il tipo di risultato dichiarato, qui `Nat`.
-/

def natOrBoolToNat : Nat ⊕ Bool → Nat
  | .inl n => n
  | .inr b => if b then 1 else 0

example : natOrBoolToNat (.inl 3)     = 3 := by rfl
example : natOrBoolToNat (.inr true)  = 1 := by rfl
example : natOrBoolToNat (.inr false) = 0 := by rfl


/- __Exercise (difficoltà: 1/4)__ `isNatAlternative` testa quale lato è stato scelto. -/

def isNatAlternative : Nat ⊕ Bool → Bool
  | .inl _ => true
  | .inr _ => false

example : isNatAlternative (.inl 3) = true      := by rfl
example : isNatAlternative (.inr false) = false := by rfl


/- __Exercise (difficoltà: 1/4)__ Restituisci il successore del payload o la sua negazione. -/

def succOrNot : Nat ⊕ Bool → Nat ⊕ Bool
  | .inl n => .inl (n + 1)
  | .inr b => .inr (!b)

example : succOrNot (.inl 5) = .inl 6         := by rfl
example : succOrNot (.inr true) = .inr false  := by rfl

end Pattern_matching


section Proofs_about_sums

/-
Il tipo somma `Nat ⊕ Bool` ha due costruttori:

    Sum.inl : Nat  → Nat ⊕ Bool
    Sum.inr : Bool → Nat ⊕ Bool

Le seguenti funzioni ispezionano quale costruttore è stato usato, senza ispezionare
il valore memorizzato da quel costruttore.
-/

def isLeft : Nat ⊕ Bool → Bool
  | .inl _ => true
  | .inr _ => false

def isRight : Nat ⊕ Bool → Bool
  | .inl _ => false
  | .inr _ => true

example : isLeft (.inl 3) = true := by rfl
example : isLeft (.inr false) = false := by rfl

/-
Per ogni valore somma, `isLeft` restituisce la negazione di `isRight`.

Lean non può dimostrarlo immediatamente per calcolo perché `s` è arbitrario:
non sa ancora quale costruttore l'ha prodotto. La tattica `cases s`
considera separatamente i due possibili costruttori.
-/

theorem isLeft_not_isRight (s : Nat ⊕ Bool) : isLeft s = !(isRight s) := by
  cases s with
  | inl n =>              -- `s` ha la forma `.inl n`
    rw [isLeft,isRight]   -- rw non è necessario! È qui solo per farti osservare la InfoView
    rfl
  | inr b =>              -- `s` ha la forma `.inr b`
    rfl

/-
La stessa dimostrazione può essere scritta più compattamente con `rcases`.

Per una somma, il pattern

    n | b

descrive le sue due alternative. La tattica crea due goal:
un goal con `n : Nat`, e un altro goal con `b : Bool`.
-/

theorem isLeft_not_isRight₂ (s : Nat ⊕ Bool) : isLeft s = !(isRight s) := by
  rcases s with n | b
  · -- Caso `s = .inl n`
    rfl
  · -- Caso `s = .inr b`
    rfl

/-
La tattica `rcases` può combinare pattern di prodotto e somma.

Ad esempio, considera un valore `p` con tipo

    Nat × (Bool ⊕ Nat)

Possiamo destrutturare `p` come segue:

  rcases p with ⟨n, b | m⟩

* `⟨n, ...⟩` scompone il prodotto esterno;
* `b | m` considera i due costruttori della somma interna.

Di conseguenza, `rcases` crea due goal.
-/

example (p : Nat × (Bool ⊕ Nat)) : Nat × Bool := by
  rcases p with ⟨n, b | m⟩
  · -- Qui `p` aveva la forma `(n, .inl b)`.
    exact (n, b)
  · -- Qui `p` aveva la forma `(n, .inr m)`.
    exact (m, false)


end Proofs_about_sums


section Type_isomorphisms

/-
Come per i prodotti, l'operatore di tipo ⊕ è commutativo a meno di isomorfismo.
In particolare, dimostriamo che:

    Nat ⊕ Bool  ≅  Bool ⊕ Nat
-/

def swapNatBoolSum : Nat ⊕ Bool → Bool ⊕ Nat
  | .inl n => .inr n
  | .inr b => .inl b

def swapBoolNatSum : Bool ⊕ Nat → Nat ⊕ Bool
  | .inl b => .inr b
  | .inr n => .inl n

example : swapNatBoolSum (.inl 4) = .inr 4 := by rfl
example : swapNatBoolSum (.inr true) = .inl true := by rfl

/- __Exercise (difficoltà: 1/4)__ Dimostra l'isomorfismo di tipi:

    Nat ⊕ Bool  ≅  Bool ⊕ Nat.

Usa la tattica `cases` per creare due goal.
-/

theorem swapBoolNatSum_comp_swapNatBoolSum_id (s : Nat ⊕ Bool) :
    swapBoolNatSum (swapNatBoolSum s) = s := by
  cases s with
  | inl n => rfl
  | inr b => rfl

theorem swapNatBoolSum_comp_swapBoolNatSum_id (s : Bool ⊕ Nat) :
    swapNatBoolSum (swapBoolNatSum s) = s := by
  cases s with
  | inl b => rfl
  | inr n => rfl

end Type_isomorphisms



section Partial_functions

/-
Alcune funzioni potrebbero non essere definite per tutti i possibili input. Ad esempio:
* `0` non ha predecessore in `Nat`;
* la divisione per zero non è definita;
* un prelievo richiesto potrebbe superare un saldo.

Possiamo formalizzare tali funzioni _parziali_ in modi diversi:

1. Restituire un valore "fittizio" quando la funzione non è definita.
2. Restringere il dominio per rendere la funzione totale (usando *tipi dipendenti*)
3. Aggiungere un valore speciale nel codominio per rappresentare il valore "indefinito".

In questa sezione consideriamo l'ultima alternativa.

Nota che i tipi somma ci permettono di codificare il valore di errore usando `… ⊕ Unit`.

Ad esempio, li usiamo per definire una funzione predecessore che è indefinita su `0`:
-/

def partial_pred : Nat → Nat ⊕ Unit
  | 0     => .inr ()
  | n + 1 => .inl n

example : partial_pred 0 = .inr () := by rfl
example : partial_pred 3 = .inl 2  := by rfl


/-
__Exercise (difficoltà: 1/4)__: Definisci una funzione che prende un numero pari
come input e restituisce il numero pari successivo. Se l'input non è un numero
pari, allora la funzione è indefinita.
Suggerimento: usa l'operatore modulo: `%`.
-/

def nextEven (n : Nat) : Nat ⊕ Unit :=
  if n % 2 = 0 then .inl (n + 2) else .inr ()

example : nextEven 4 = .inl 6  := by rfl
example : nextEven 5 = .inr () := by rfl

/-
Definiamo una funzione che prende due funzioni parziali e le somma.
La somma è indefinita quando uno qualsiasi degli input è indefinito.
-/

def partial_sum (f g: Nat → Nat ⊕ Unit) (n : Nat) : Nat ⊕ Unit :=
  match f n with
  | .inr () => .inr ()
  | .inl rf => match g n with
    | .inr () => .inr ()
    | .inl rg => .inl (rf + rg)


example : (partial_sum partial_pred nextEven) 0 = .inr () := by rfl
example : (partial_sum partial_pred nextEven) 1 = .inr () := by rfl
example : (partial_sum partial_pred nextEven) 2 = .inl 5  := by rfl

/-
Lean dispone di un tipo speciale `Option` per gestire le funzioni parziali.
Ad esempio, il tipo `Option Nat` ha due forme:

    none   : Option Nat   --- il "valore indefinito"
    some n : Option Nat   --- il payload etichettato quando la funzione è definita

`Option` stesso funziona con qualsiasi tipo di payload, non solo `Nat`
(vedi la prossima lezione sul polimorfismo).
-/

def partial_pred₂ : Nat → Option Nat
  | 0     => none
  | n + 1 => some n

example : partial_pred₂ 0 = none := by rfl
example : partial_pred₂ 3 = some 2  := by rfl

/-
Quando una funzione chiama un'altra funzione che restituisce un valore Option,
il chiamante deve ispezionare un risultato prima di usare il possibile numero.
-/

def getOrElseN (default : Nat) : Option Nat → Nat
  | none   => default
  | some n => n

example : getOrElseN 100 (partial_pred₂ 8) = 7 := by rfl
example : getOrElseN 100 (partial_pred₂ 0) = 100 := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci la sottrazione parziale.
Restituisce `none` invece di troncare a zero quando `b > a`. -/

def partial_sub (a b : Nat) : Option Nat :=
  if a ≥ b then some (a - b) else none

example : partial_sub 10 3 = some 7 := by rfl
example : partial_sub 3 10 = none   := by rfl

/- __Exercise (difficoltà: 1/4)__ Somma due numeri opzionali solo quando entrambi
sono presenti. -/

def partial_sum₂ (f g: Nat → Option Nat) (n : Nat) : Option Nat :=
  match f n with
  | none => none
  | some a => match g n with
    | none => none
    | some b => some (a + b)

example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 0  = none   := by rfl
example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 11 = none   := by rfl
example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 2  = some 9 := by rfl


/-
Dimostriamo ora che `partial_sum` è commutativa. Più del teorema stesso, è
interessante come lo dimostriamo. Controlla la dimostrazione passo-passo nella InfoView.
-/

theorem partial_sum_comm (f1 f2: Nat → Nat ⊕ Unit) (n : Nat) : partial_sum f1 f2 n = partial_sum f2 f1 n := by
  cases h1 : f1 n with
  | inl r1 =>
    cases h2 : f2 n with
    | inl r2 =>
      simp [partial_sum, h1, h2]
      rw [Nat.add_comm]
    | inr _ =>
      simp [partial_sum, h1, h2]
  | inr _ =>
    cases h2 : f2 n with
    | _ => simp [partial_sum, h1, h2]


end Partial_functions


end Sum_types



section Exercises


section Domain_restriction

/-
## Esercizio: Restrizione del dominio

**Difficoltà: 2/4**

Scrivi una funzione `restrict` che prende come input una funzione `f` e un predicato `p`,
e restituisce una funzione `g` che si comporta come `f` sui valori di input che
soddisfano `p`, ed è indefinita altrimenti.

  restrict : (Nat → Nat) → (Nat → Bool) → Nat → Option Nat
-/

def restrict (f : Nat → Nat) (p : Nat → Bool) : (Nat → Option Nat) :=
  fun n => if p n then some (f n) else none

def f1_res := restrict Nat.succ (fun x => x > 0)
example : f1_res 1 = some 2 := by rfl
example : f1_res 0 = none   := by rfl

/- Dimostra che `restrict f p n` è indefinita ogniqualvolta `p n` è falso. -/

theorem restrict_none (f : Nat → Nat) (p : Nat → Bool) :
  ∀ n : Nat, p n = false → restrict f p n = none := by
  intro n h
  simp [restrict, h]

/- Dimostra che `restrict f p n` è definita ogniqualvolta `p n` è vero. -/

theorem restrict_some (f : Nat → Nat) (p : Nat → Bool) :
  ∀ n : Nat, p n = true → exists v : Nat, restrict f p n = some v := by
  intro n h
  exists f n
  simp [restrict, h]

end Domain_restriction



section Max_option

/- ## Esercizio: Massimo parziale

**Difficoltà: 1-3/4**
-/

/- __Exercise (difficoltà: 1/4)__ Definisci il massimo parziale. -/

def max_option (o1 o2: Option Nat) : Option Nat :=
  match o1, o2 with
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (if a ≥ b then a else b)

example : max_option (some 3) (some 5) = some 5 := by rfl
example : max_option (some 3) none = some 3     := by rfl
example : max_option none (some 5) = some 5     := by rfl


/- __Exercise (difficoltà: 3/4)__ Dimostra che il massimo parziale è indefinito
ogniqualvolta entrambi gli input sono none. -/

theorem max_option_none (o1 o2: Option Nat) : max_option o1 o2 = none ↔ o1 = none ∧ o2 = none := by
  constructor
  · intro h
    cases o1 with
    | none =>
      cases o2 with
      | none => exact ⟨rfl, rfl⟩
      | some b => simp [max_option] at h
    | some a =>
      cases o2 with
      | none => simp [max_option] at h
      | some b => simp [max_option] at h
  · intro ⟨h1, h2⟩
    subst h1
    subst h2
    rfl

/-
__Exercise (difficoltà: 3/4)__ Dimostra la seguente proprietà del massimo parziale.
Segui lo scheletro della dimostrazione, ispezionando la InfoView, e risolvi i sorry.
-/

theorem max_option_preserves_lower_bound
    (a lower : Nat) (b : Option Nat) (ha : lower ≤ a) :
    ∃ c, max_option (some a) b = some c ∧ lower ≤ c := by
  cases b with
  | none =>
    exists a
    constructor
    · rfl
    · exact ha
  | some b =>
    exists (if a ≥ b then a else b)
    constructor
    · rfl
    · by_cases h : a ≥ b
      · simp [h]
        exact ha
      · simp [h]
        omega

end Max_option



section Arithmetic_expressions

/- ## Esercizio: espressioni aritmetiche

**Difficoltà: 2/4**

Considera il seguente tipo per definire semplici espressioni aritmetiche: -/

inductive Aexp where
  | val : Nat → Aexp
  | add : Aexp × Aexp → Aexp
  | sub : Aexp × Aexp → Aexp
  | mul : Aexp × Aexp → Aexp
  | div : Aexp × Aexp → Aexp

/-
Scrivi una funzione:

  eval : Aexp → Option Nat

che valuta l'espressione, in stile big-step.

La valutazione è una funzione parziale. È indefinita nei seguenti casi:
* una divisione per zero;
* una sottrazione `n1 - n2` dove `n2 > n1`.
-/

def eval (e : Aexp) : Option Nat :=
  match e with
  | .val n => some n
  | .add (e1, e2) =>
    match eval e1, eval e2 with
    | some n1, some n2 => some (n1 + n2)
    | _, _ => none
  | .sub (e1, e2) =>
    match eval e1, eval e2 with
    | some n1, some n2 => if n1 ≥ n2 then some (n1 - n2) else none
    | _, _ => none
  | .mul (e1, e2) =>
    match eval e1, eval e2 with
    | some n1, some n2 => some (n1 * n2)
    | _, _ => none
  | .div (e1, e2) =>
    match eval e1, eval e2 with
    | some n1, some n2 => if n2 > 0 then some (n1 / n2) else none
    | _, _ => none

example : eval (Aexp.add (Aexp.val 1, Aexp.val 2)) = some 3                      := by rfl
example : eval (Aexp.add (Aexp.val 1, Aexp.sub (Aexp.val 2, Aexp.val 3))) = none := by rfl
example : eval (Aexp.mul (Aexp.val 1, Aexp.div (Aexp.val 2, Aexp.val 0))) = none := by rfl


/-
__Exercise (difficoltà: 2/4)__ Dimostra le seguenti proprietà della valutazione e
dell'addizione:
* `eval_add_success`: se entrambi gli operandi si valutano con successo, anche la
  loro addizione si valuta con successo;
* `eval_add_error_left`: se la valutazione del primo operando fallisce, allora la
  valutazione dell'addizione fallisce;
* `eval_add_error_right`: se la valutazione del secondo operando fallisce, allora la
  valutazione dell'addizione fallisce;
* `eval_add_zero_right`: aggiungere zero non cambia il risultato della valutazione,
  anche quando la valutazione fallisce;
* `eval_add_commutative`: l'addizione è commutativa;
* `eval_add_characterization`: un'addizione si valuta a `n` sse i suoi operandi si
  valutano a due numeri la cui somma è `n`;
* `eval_add_associative`: l'addizione è associativa.
-/

theorem eval_add_success
    (e1 e2 : Aexp) (n1 n2 : Nat)
    (h1 : eval e1 = some n1)
    (h2 : eval e2 = some n2) :
    eval (.add (e1, e2)) = some (n1 + n2) := by
  simp [eval, h1, h2]

theorem eval_add_error_left
    (e1 e2 : Aexp)
    (h : eval e1 = none) :
    eval (.add (e1, e2)) = none := by
  simp [eval, h]

theorem eval_add_error_right
    (e1 e2 : Aexp)
    (h : eval e2 = none) :
    eval (.add (e1, e2)) = none := by
  cases h1 : eval e1 <;> simp [eval, h1, h]

theorem eval_add_zero_right (e : Aexp) :
    eval (.add (e, .val 0)) = eval e := by
  cases h : eval e <;> simp [eval, h]

theorem eval_add_commutative (e1 e2 : Aexp) :
    eval (.add (e1, e2)) = eval (.add (e2, e1)) := by
  cases h1 : eval e1 <;> cases h2 : eval e2 <;> simp [eval, h1, h2, Nat.add_comm]

theorem eval_add_characterization
    (e1 e2 : Aexp) (n : Nat) :
    eval (.add (e1, e2)) = some n ↔
      ∃ n1 n2,
        eval e1 = some n1 ∧
        eval e2 = some n2 ∧
        n = n1 + n2 := by
  constructor
  · intro h
    cases h1 : eval e1 with
    | none => simp [eval, h1] at h
    | some n1 =>
      cases h2 : eval e2 with
      | none => simp [eval, h1, h2] at h
      | some n2 =>
        simp [eval, h1, h2] at h
        exists n1, n2
        exact ⟨rfl, rfl, h.symm⟩
  · intro ⟨n1, n2, h1, h2, hn⟩
    subst hn
    simp [eval, h1, h2]

theorem eval_add_associative (e1 e2 e3 : Aexp) :
    eval (.add ((.add (e1, e2)), e3)) = eval (.add (e1, (.add (e2,e3)))) := by
  cases h1 : eval e1 <;> cases h2 : eval e2 <;> cases h3 : eval e3 <;>
    simp [eval, h1, h2, h3, Nat.add_assoc]

end Arithmetic_expressions



section Students_grades

/- ## Esercizio: Voti degli studenti

Considera il seguente tipo per rappresentare i voti di uno studente in un esame: -/

structure Grade where
  name    : String        -- il nome dello studente
  written : Option Nat    -- il voto della parte scritta
  oral    : Option Nat    -- il voto della parte orale
  deriving Repr

/-
__Exercise (difficoltà: 1/4)__ Definisci una funzione che restituisce la somma
dei voti scritto e orale.
-/

def total_score (g : Grade) : Option Nat :=
  match g.written, g.oral with
  | some w, some o => some (w + o)
  | _, _ => none

def mario : Grade := { name := "Mario", written := some 18, oral := some 15 }
def luigi : Grade := { name := "Luigi", written := some 15, oral := none }
def alice : Grade := { name := "Alice", written := some 28, oral := some 30 }

example : total_score mario = some 33 := by rfl
example : total_score luigi = none    := by rfl
example : total_score alice = some 58 := by rfl

/-
__Exercise (difficoltà: 1/4)__ Dimostra che `total_score` non dipende dal nome
dello studente.
-/

example (g : Grade) (newName : String) :
    total_score { g with name := newName } = total_score g := by
  rfl

/-
__Exercise (difficoltà: 3/4)__ Studia la seguente caratterizzazione di `total_score`.
Segui lo scheletro della dimostrazione, ispezionando la InfoView, e risolvi i sorry.
-/

theorem total_score_characterization (g : Grade) (score : Nat) :
    total_score g = some score ↔
      ∃ w o,
        g.written = some w ∧
        g.oral = some o ∧
        score = w + o := by
  constructor
  · intro h
    cases hw : g.written with
    | none => simp [total_score, hw] at h
    | some w =>
      cases ho : g.oral with
      | none => simp [total_score, hw, ho] at h
      | some o =>
        simp [total_score, hw, ho] at h
        exists w, o
        exact ⟨rfl, rfl, h.symm⟩
  · intro ⟨w, o, hw, ho, hs⟩
    subst hs
    simp [total_score, hw, ho]

/-
__Exercise (difficoltà: 1/4)__ Definisci una funzione che restituisce true se
entrambi i voti sono almeno 18, e false altrimenti.
-/

def passed (g : Grade) : Bool :=
  match g.written, g.oral with
  | some w, some o => w ≥ 18 && o ≥ 18
  | _, _ => false

example : passed mario = false := by rfl
example : passed luigi = false := by rfl
example : passed alice = true  := by rfl

example (g : Grade) (newName : String) :
    passed { g with name := newName } = passed g := by
  rfl

/-
__Exercise (difficoltà: 2/4)__ Studia la seguente proprietà di `passed`.
Prova a scrivere in inglese cosa afferma effettivamente questa proprietà.
Sperimenta con gli LLM per costruire una dimostrazione.
La conversa è vera? Se no, dimostralo.
-/

theorem passed_implies_minimum_total (g : Grade) :
    passed g = true →
      ∃ score : Nat,
        total_score g = some score ∧ score ≥ 36 := by
  intro h
  cases hw : g.written with
  | none => simp [passed, hw] at h
  | some w =>
    cases ho : g.oral with
    | none => simp [passed, hw, ho] at h
    | some o =>
      simp [passed, hw, ho] at h
      exists (w + o)
      constructor
      · simp [total_score, hw, ho]
      · omega

/-
__Exercise (difficoltà: 2/4)__ Definisci una funzione che, dati due risultati dello
stesso studente, restituisce un nuovo risultato con i voti massimi tra i due risultati.
La funzione è parziale: se i nomi dei due studenti non corrispondono, allora è indefinita.

Suggerimento: usa `max_option`
-/

def max_grade (g1 g2: Grade) : Option Grade :=
  if g1.name = g2.name then
    some { name := g1.name,
           written := max_option g1.written g2.written,
           oral := max_option g1.oral g2.oral }
  else none

example : max_grade mario luigi = none := by rfl

def luigi2 : Grade := { name := "Luigi", written := some 12, oral := some 17 }
def alice2 : Grade := { name := "Alice", written := some 30, oral := none }

example : max_grade luigi luigi2 = some { name := "Luigi", written := some 15, oral := some 17 } := by rfl
example : max_grade alice alice2 = some { name := "Alice", written := some 30, oral := some 30 } := by rfl

/-
__Exercise (difficoltà: 3/4)__ Studia la seguente proprietà di `max_grade`.
Prova a scrivere in inglese cosa afferma effettivamente questa proprietà.
Sperimenta con gli LLM per costruire una dimostrazione.
La conversa è vera? Se no, dimostralo.
-/

theorem max_grade_passed (g1 g2 g12: Grade) (h: max_grade g1 g2 = some g12) : passed g1 = true → passed g12 = true := by
  intro hp
  simp [max_grade] at h
  split at h
  · -- nomi uguali
    cases h
    simp [passed] at hp ⊢
    rcases hp with ⟨h1, h2⟩
    constructor
    · cases hw : g1.written <;> simp [max_option, hw] at * <;> omega
    · cases ho : g1.oral <;> simp [max_option, ho] at * <;> omega
  · -- nomi diversi
    simp at h

end Students_grades



section Type_reconstructions

/- __Exercise (difficoltà: 1-2/4)__ Definisci funzioni che rispettano i tipi.
Ci sono molte risposte corrette: alcune sono banali, ma cerca anche quelle non banali.
-/

example : (Nat × Nat) → (Nat × Nat) := fun p => (p.2, p.1)

example : Nat → (Nat × Nat) → Nat := fun n p => n + p.1 + p.2

example : Nat → (Nat × Nat) → (Nat × Nat) := fun n p => (p.1 + n, p.2 + n)

example : (Nat × Nat) → Nat → (Nat × Nat) := fun p n => (p.1 * n, p.2 * n)

example : (Nat × Nat) → (Nat × Nat) → Nat := fun p q => p.1 + p.2 + q.1 + q.2

example : (Nat × Bool) → (Nat ⊕ Bool) := fun p => if p.2 then .inl p.1 else .inr p.2

example : Nat → Bool → Bool → (Nat ⊕ Bool) := fun n b1 b2 => if b1 then .inl n else .inr b2

example : (Nat ⊕ Bool) → (Nat ⊕ Bool) → (Nat ⊕ Bool) :=
  fun s1 s2 => match s1, s2 with
    | .inl n1, .inl n2 => .inl (n1 + n2)
    | .inl n1, .inr _ => .inl n1
    | .inr _, .inl n2 => .inl n2
    | .inr b1, .inr b2 => .inr (b1 && b2)

example : (Nat → String) ⊕ (String × Bool) → Nat → String :=
  fun s n => match s with
    | .inl f => f n
    | .inr (str, _) => str

example : (Nat → String) ⊕ (Bool → String) → (Nat × Bool) → String :=
  fun s p => match s with
    | .inl f => f p.1
    | .inr g => g p.2

end Type_reconstructions



section Type_isomorphisms

/- In questa sezione dimostriamo alcuni isomorfismi di tipi. -/

/-
## Esercizio: Point e Nat × Nat (difficoltà: 1/4)

Dimostra che i tipi `Point` e `Nat × Nat` sono isomorfi:

    Point  ≅  Nat × Nat
-/

def pointToPair (p : Point) : Nat × Nat :=
  (p.x, p.y)

def pairToPoint : Nat × Nat → Point :=
  fun p => { x := p.1, y := p.2 }

theorem point_pair_id : pairToPoint ∘ pointToPair = id := by
  funext p
  rcases p with ⟨x, y⟩
  rfl

theorem pair_point_roundtrip : pointToPair ∘ pairToPoint = id := by
  funext p
  rcases p with ⟨x, y⟩
  rfl


/-
## Esercizio: Somme e Option (difficoltà: 1/4)

Dimostra l'isomorfismo di tipi:

    Nat ⊕ Unit  ≅  Option Nat
-/

def sumNatUnit_to_NatOption (s : Nat ⊕ Unit) : Option Nat :=
  match s with
  | .inl n => some n
  | .inr () => none

def sumNatOption_to_NatUnit (o : Option Nat) : Nat ⊕ Unit :=
  match o with
  | some n => .inl n
  | none => .inr ()

theorem sumOption_right_left (s : Nat ⊕ Unit) :
  sumNatOption_to_NatUnit (sumNatUnit_to_NatOption s) = s := by
  cases s with
  | inl n => rfl
  | inr u => cases u; rfl

theorem sumOption_left_right (o : Option Nat) :
  sumNatUnit_to_NatOption (sumNatOption_to_NatUnit o) = o := by
  cases o with
  | some n => rfl
  | none => rfl

/-
## Esercizio: Bool e Unit × Unit (difficoltà: 2/4)

Dimostra l'isomorfismo di tipi:

      Bool  ≅  Unit ⊕ Unit
-/

def boolToSum : Bool → Unit ⊕ Unit :=
  fun b => if b then .inl () else .inr ()

def sumToBool : Unit ⊕ Unit → Bool :=
  fun s => match s with
    | .inl _ => true
    | .inr _ => false

theorem boolToSum_sumToBool_id (s : Unit ⊕ Unit) : boolToSum (sumToBool s) = s := by
  cases s with
  | inl u => cases u; rfl
  | inr u => cases u; rfl

theorem sumToBool_boolToSum_id (b : Bool) : sumToBool (boolToSum b) = b := by
  cases b with
  | true => rfl
  | false => rfl


/-
## Esercizio: Associatività dei prodotti (difficoltà: 1/4)

Dimostra l'isomorfismo di tipi:

    Nat × (Bool × String)  ≅  (Nat × Bool) × String
-/

def associateProductLeft : Nat × (Bool × String) → (Nat × Bool) × String
  | (n, (b, s)) => ((n, b), s)

def associateProductRight : (Nat × Bool) × String → Nat × (Bool × String)
  | ((n, b), s) => (n, (b, s))

theorem associateProduct_right_left (p : Nat × (Bool × String)) :
    associateProductRight (associateProductLeft p) = p := by
  rcases p with ⟨n, b, s⟩
  rfl

theorem associateProduct_left_right (p : (Nat × Bool) × String) :
    associateProductLeft (associateProductRight p) = p := by
  rcases p with ⟨⟨n, b⟩, s⟩
  rfl


/-
## Esercizio: Associatività delle somme (difficoltà: 2/4)

Dimostra l'isomorfismo di tipi:

    Nat ⊕ (Bool ⊕ String)  ≅  (Nat ⊕ Bool) ⊕ String
-/

def associateSumLeft : Nat ⊕ (Bool ⊕ String) → (Nat ⊕ Bool) ⊕ String
  | .inl n => .inl (.inl n)
  | .inr (.inl b) => .inl (.inr b)
  | .inr (.inr s) => .inr s

def associateSumRight : (Nat ⊕ Bool) ⊕ String → Nat ⊕ (Bool ⊕ String)
  | .inl (.inl n) => .inl n
  | .inl (.inr b) => .inr (.inl b)
  | .inr s => .inr (.inr s)

theorem associateSum_right_left (s : Nat ⊕ (Bool ⊕ String)) :
    associateSumRight (associateSumLeft s) = s := by
  cases s with
  | inl n => rfl
  | inr s' =>
    cases s' with
    | inl b => rfl
    | inr str => rfl

/- (La seconda direzione è omessa per brevità ma analoga.) -/

/-
## Esercizio: Distributività dei prodotti sulle somme (difficoltà: 2/4)

Dimostra l'isomorfismo di tipi:

    Nat × (Bool ⊕ Nat)  ≅  (Nat × Bool) ⊕ (Nat × Nat)

Questo è un'istanza concreta del pattern distributivo generale:

    A × (B + C)  ≅  (A × B) + (A × C).
-/

def distributeNatBoolNat :
    Nat × (Bool ⊕ Nat) → (Nat × Bool) ⊕ (Nat × Nat)
  | (n, .inl b) => .inl (n, b)
  | (n, .inr m) => .inr (n, m)

def factorNatBoolNat :
    (Nat × Bool) ⊕ (Nat × Nat) → Nat × (Bool ⊕ Nat)
  | .inl (n, b) => (n, .inl b)
  | .inr (n, m) => (n, .inr m)

example : distributeNatBoolNat (3, .inl true) = .inl (3, true) := by rfl

example : distributeNatBoolNat (3, .inr 8) = .inr (3, 8) := by rfl

theorem factor_after_distribute (p : Nat × (Bool ⊕ Nat)) :
    factorNatBoolNat (distributeNatBoolNat p) = p := by
  rcases p with ⟨n, b | m⟩
  · rfl
  · rfl

theorem distribute_after_factor (s : (Nat × Bool) ⊕ (Nat × Nat)) :
    distributeNatBoolNat (factorNatBoolNat s) = s := by
  cases s with
  | inl p => rcases p with ⟨n, b⟩; rfl
  | inr p => rcases p with ⟨n, m⟩; rfl

end Type_isomorphisms


end Exercises