import PL_Lean.PL07_Prop


/-
# Esercizi sulla logica proposizionale e l'isomorfismo di Curry-Howard
-/

section Exercises


section Permutation_combinator

/- ## Combinatore di permutazione (difficoltà: 2/4)

Dimostra che l'ordine delle due ipotesi di una funzione curried può essere scambiato.
Dai sia la dimostrazione tattica che quella termine.
-/

theorem flip_term {P Q R : Prop} : (P → Q → R) → Q → P → R :=
  fun f q p => f p q

theorem flip_tac {P Q R : Prop} : (P → Q → R) → Q → P → R := by
  intro f q p
  apply f
  · exact p
  · exact q

end Permutation_combinator



section S_combinator

/- ## Combinatore S (difficoltà: 2/4)

Dimostra il combinatore S del lambda-calcolo, sia in modalità tattica che termine:

    (P → Q → R) → (P → Q) → P → R  .

Suggerimento: `apply f` produce *due* goal, uno per ciascun argomento di `f`; usa un bullet `·`
per ciascuno di essi.
-/

theorem s_term {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R :=
  fun f g p => f p (g p)

theorem s_tac {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R := by
  intro f g p
  apply f
  · exact p
  · apply g
    exact p

end S_combinator



section Conjunction_associativity

/- ## Associatività della congiunzione (difficoltà: 2/4)

Dimostra sia la versione sui dati che quella logica, ciascuna in modalità tattica e termine.
-/

def assoc_prod_tac {A B C : Type} : (A × B) × C → A × (B × C) := by
  intro h
  rcases h with ⟨⟨a, b⟩, c⟩
  exact ⟨a, ⟨b, c⟩⟩

def assoc_prod_term {A B C : Type} : (A × B) × C → A × (B × C) :=
  fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩

theorem and_assoc_tac {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro h
  rcases h with ⟨⟨p, q⟩, r⟩
  exact ⟨p, ⟨q, r⟩⟩

theorem and_assoc_term {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  fun ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩


end Conjunction_associativity


section Disjunction_associativity

/- ## Associatività della disgiunzione (difficoltà: 3/4)

Dimostra l'associatività della disgiunzione in modalità tattica e termine.
Suggerimento: in modalità tattica, `rcases h with p | q | r` divide i tre casi di
`P ∨ (Q ∨ R)` in una volta, e ogni goal necessita una diversa sequenza di `left` e `right`;
in modalità termine, usa un `match` con tre rami e pattern annidati come
`Or.inr (Or.inl q)`.
-/

theorem or_assoc_tac {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  intro h
  rcases h with p | q | r
  · left
    left
    exact p
  · left
    right
    exact q
  · right
    exact r

theorem or_assoc_term {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
  fun h => match h with
  | .inl p => .inl (.inl p)
  | .inr (.inl q) => .inl (.inr q)
  | .inr (.inr r) => .inr r

end Disjunction_associativity


section Distributivity

/- ## Distributività (difficoltà: 2/4)

Dimostra le seguenti leggi di distributività, prima sui dati e poi sulle proposizioni.
-/

def distr_term {A B C : Type} : A × (B ⊕ C) → (A × B) ⊕ (A × C)
  | (a, .inl b) => .inl (a, b)
  | (a, .inr c) => .inr (a, c)

theorem and_or_tac {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h with ⟨p, q | r⟩
  · left
    exact ⟨p, q⟩
  · right
    exact ⟨p, r⟩

theorem and_or_term {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  fun h => match h with
  | ⟨p, .inl q⟩ => .inl ⟨p, q⟩
  | ⟨p, .inr r⟩ => .inr ⟨p, r⟩

theorem or_and_tac {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) := by
  intro h
  rcases h with ⟨p | q, r⟩
  · left
    exact ⟨p, r⟩
  · right
    exact ⟨q, r⟩

theorem or_and_term {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) :=
  fun h => match h with
  | ⟨.inl p, r⟩ => .inl ⟨p, r⟩
  | ⟨.inr q, r⟩ => .inr ⟨q, r⟩

end Distributivity


section Triple_negation

/- ## Tripla negazione (difficoltà: 2/4)

Dimostra che la tripla negazione collassa: `¬¬¬P → ¬P`. -/

theorem not_not_not_tac {P : Prop} : ¬¬¬P → ¬P := by
  intro h p
  apply h
  intro np
  exact np p

theorem not_not_not_term {P : Prop} : ¬¬¬P → ¬P :=
  fun h p => h (fun np => np p)

end Triple_negation


section De_Morgan_Laws

/- ## Leggi di De Morgan (difficoltà: 3/4)

Dimostra la legge di De Morgan per la disgiunzione, in entrambe le direzioni.
-/

theorem not_or_tac {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  · intro p
    apply h
    left
    exact p
  · intro q
    apply h
    right
    exact q

theorem not_or_term {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun h => ⟨fun p => h (.inl p), fun q => h (.inr q)⟩

theorem and_not_tac {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro h pq
  rcases h with ⟨np, nq⟩
  rcases pq with p | q
  · exact np p
  · exact nq q

theorem and_not_term {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun ⟨np, nq⟩ pq => match pq with
  | .inl p => np p
  | .inr q => nq q

/- L'implicazione conversa, `¬(P ∧ Q) → ¬P ∨ ¬Q`, **non** è costruttivamente dimostrabile. -/

theorem not_and_tac {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  intro h pq
  rcases h with np | nq
  · exact np pq.1
  · exact nq pq.2

theorem not_and_term {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun h pq => match h with
  | .inl np => np pq.1
  | .inr nq => nq pq.2

end De_Morgan_Laws


section Iff

/-
## Se e solo se (difficoltà: 2-3/4)

`P ↔ Q` significa `(P → Q) ∧ (Q → P)`. In Lean è una struttura con due campi, `mp`
(l'implicazione in avanti) e `mpr` (quella all'indietro). Quindi una dimostrazione di `P ↔ Q` è una
**coppia di funzioni**, esattamente come un isomorfismo di tipi `A ≃ B` è una coppia di funzioni
`A → B` e `B → A` (laboratorio precedente).

La proposizione `True` ha esattamente una dimostrazione, `True.intro` (la tattica `trivial` la trova).
Corrisponde al tipo `Unit`, il cui unico valore è `()`.
-/

#check and_swap_tac

theorem and_swap_iff_tac {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

theorem and_swap_iff_term {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩



/- Dimostra l'equivalenza tra "`P` e `Q` implicano
`R`" e "`P` implica (`Q` implica `R`)". Dimostrazione tattica e termine.
Suggerimento: hai dimostrato entrambe le direzioni prima (`curry_tac`, `uncurry_tac`); puoi riusarle,
o scrivere la dimostrazione da zero. Leggi le due dimostrazioni di ciascuna direzione con
`#print`. -/

theorem curry_iff_tac {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro f p q
    exact f ⟨p, q⟩
  · intro f h
    exact f h.1 h.2

theorem curry_iff_term {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) :=
  ⟨fun f p q => f ⟨p, q⟩, fun f h => f h.1 h.2⟩


/- __Exercise (difficoltà: 2/4)__ Combina i tuoi teoremi di De Morgan in una singola
equivalenza: `¬(P ∨ Q) ↔ ¬P ∧ ¬Q`. Dimostrazione tattica e termine. -/

theorem de_morgan_tac {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · exact not_or_tac
  · exact and_not_tac

theorem de_morgan_term {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  ⟨not_or_term, and_not_term⟩

end Iff

end Exercises