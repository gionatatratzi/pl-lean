import PL_Lean.PL07_Prop


/-
# Exercises on propositional logic and the Curry-Howard isomorphism
-/

section Exercises


section Permutation_combinator

/- ## Permutation combinator (difficulty: 2/4)

Prove that the order of the two hypotheses of a curried function can be swapped.
Give both tactic proof and term proof.
-/

theorem flip_term {P Q R : Prop} : (P → Q → R) → Q → P → R :=
  fun f q p => f p q

theorem flip_tac {P Q R : Prop} : (P → Q → R) → Q → P → R := by
  intro f q p
  exact f p q

end Permutation_combinator



section S_combinator

/- ## S combinator (difficulty: 2/4)

Prove the S combinator of the lambda-calculus, both in tactic and in term mode:

    (P → Q → R) → (P → Q) → P → R  .

Hint: `apply f` produces *two* goals, one for each argument of `f`; use a bullet `·`
for each of them.
-/

theorem s_term {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R :=
  fun f g p => f p (g p)

theorem s_tac {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R := by
  intro f g p
  apply f
  . exact p
  . apply g
    exact p

end S_combinator



section Conjunction_associativity

/- ## Associativity of conjunction (difficulty: 2/4)

Prove both the data version and the logical version, each in tactic mode and in term mode.
-/

def assoc_prod_tac {A B C : Type} : (A × B) × C → A × (B × C) := by
  intro h
  rcases h with ⟨⟨a, b⟩, c⟩
  constructor
  . exact a
  . constructor
    . exact b
    . exact c

def assoc_prod_term {A B C : Type} : (A × B) × C → A × (B × C) :=
  fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩

theorem and_assoc_tac {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro h
  rcases h with ⟨⟨p, q⟩, r⟩
  constructor
  . exact p
  . constructor
    . exact q
    . exact r

theorem and_assoc_term {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  fun ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩


end Conjunction_associativity


section Disjunction_associativity

/- ## Associativity of disjunction (difficulty: 3/4)

Prove associativity of disjunction in tactic mode and in term mode.
Hint: in tactic mode, `rcases h with p | q | r` splits the three cases of
`P ∨ (Q ∨ R)` at once, and each goal needs a different sequence of `left` and `right`;
in term mode, use a `match` with three branches and nested patterns such as
`Or.inr (Or.inl q)`.
-/

theorem or_assoc_tac {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  intro h
  rcases h with p | q | r
  . left
    left
    exact p
  . left
    right
    exact q
  . right
    exact r

theorem or_assoc_term {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
  fun h => match h with
  | .inl p => Or.inl (Or.inl p)
  | .inr (Or.inl q) => Or.inl (Or.inr q)
  | .inr (Or.inr r) => Or.inr r

end Disjunction_associativity


section Distributivity

/- ## Distributivity (difficulty: 2/4)

Prove the following distributivity laws, first on data and then on propositions.
-/

def distr_term {A B C : Type} : A × (B ⊕ C) → (A × B) ⊕ (A × C) :=
  fun ⟨a, h⟩ => match h with
  | .inl b => Or.inl ⟨a, b⟩
  | .inr c => Or.inr ⟨a, c⟩

theorem and_or_tac {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h with ⟨p, q_or_r⟩
  rcases q_or_r with q | r
  . left
    constructor
    . exact p
    . exact q
  . right
    constructor
    . exact p
    . exact r

theorem and_or_term {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  fun ⟨p, q_or_r⟩ => match q_or_r with
  | .inl q => Or.inl ⟨p, q⟩
  | .inr r => Or.inr ⟨p, r⟩

theorem or_and_tac {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) := by
  intro h
  rcases h with ⟨p_or_q, r⟩
  rcases p_or_q with p | q
  . left
    constructor
    . exact p
    . exact r
  . right
    constructor
    . exact q
    . exact r

theorem or_and_term {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) :=
  fun ⟨p_or_q, r⟩ => match p_or_q with
  | .inl p => Or.inl ⟨p, r⟩
  | .inr q => Or.inr ⟨q, r⟩

end Distributivity


section Triple_negation

/- ## Triple negation (difficulty: 2/4)

Prove that triple negation collapses: `¬¬¬P → ¬P`. -/

theorem not_not_not_tac {P : Prop} : ¬¬¬P → ¬P := by
  intro h
  exact h

theorem not_not_not_term {P : Prop} : ¬¬¬P → ¬P :=
  fun h => h

end Triple_negation


section De_Morgan_Laws

/- ## De Morgan's Lawas (difficulty: 3/4)

Prove De Morgan's law for disjunction, in both directions.
-/

theorem not_or_tac {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  . intro p
    apply h
    left
    exact p
  . intro q
    apply h
    right
    exact q

theorem not_or_term {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun h => ⟨fun p => h (Or.inl p), fun q => h (Or.inr q)⟩

theorem and_not_tac {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro h
  intro p_or_q
  rcases p_or_q with p | q
  . contradiction
    exact h.1 p
  . contradiction
    exact h.2 q

theorem and_not_term {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun ⟨np, nq⟩ => fun p_or_q => match p_or_q with
  | .inl p => np p
  | .inr q => nq q
/- The converse implication, `¬(P ∧ Q) → ¬P ∨ ¬Q`, is **not** constructively provable. -/

theorem not_and_tac {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  intro h
  intro p_and_q
  rcases h with np | nq
  . rcases p_and_q with ⟨p, _⟩
    exact np p
  . rcases p_and_q with ⟨_, q⟩
    exact nq q

theorem not_and_term {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun h => match h with
  | .inl np => fun ⟨p, _⟩ => np p
  | .inr nq => fun ⟨_, q⟩ => nq q

end De_Morgan_Laws


section Iff

/-
## If and only if (difficulty: 2-3/4)

`P ↔ Q` means `(P → Q) ∧ (Q → P)`.  In Lean it is a structure with two fields, `mp`
(the forward implication) and `mpr` (the backward one).  Hence a proof of `P ↔ Q` is a
**pair of functions**, exactly like a type isomorphism `A ≃ B` is a pair of functions
`A → B` and `B → A` (previous lab).

The proposition `True` has exactly one proof, `True.intro` (the tactic `trivial` finds it).
It corresponds to the type `Unit`, whose only value is `()`.
-/

#check and_swap_tac

theorem and_swap_iff_tac {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  . intro h
    rcases h with ⟨p, q⟩
    constructor
    . exact q
    . exact p
  . intro h
    rcases h with ⟨q, p⟩
    constructor
    . exact p
    . exact q

theorem and_swap_iff_term {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨fun ⟨p, q⟩ => ⟨q, p⟩, fun ⟨q, p⟩ => ⟨p, q⟩⟩



/- Prove the equivalence between "`P` and `Q` imply
`R`" and "`P` implies (`Q` implies `R`)".  Tactic proof and term proof.
Hint: you proved both directions earlier (`curry_tac`, `uncurry_tac`); you may reuse
them, or write the proof from scratch.  Read the two proofs of each direction with
`#print`. -/

theorem curry_iff_tac {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  . intro h p q
    apply h
    constructor
    . exact p
    . exact q
  . intro h pq
    rcases pq with ⟨p, q⟩
    apply h
    exact p
    exact q

theorem curry_iff_term {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) :=
  ⟨fun h p q => h ⟨p, q⟩, fun h ⟨p, q⟩ => h p q⟩


/- __Exercise (difficulty: 2/4)__ Combine your De Morgan theorems into a single
equivalence: `¬(P ∨ Q) ↔ ¬P ∧ ¬Q`.  Tactic proof and term proof. -/

theorem de_morgan_tac {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h
    exact not_or_term h
  . intro h
    exact and_not_tac h

theorem de_morgan_term {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  ⟨not_or_term, and_not_term⟩

end Iff

end Exercises
