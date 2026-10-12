import Mbekworm.Sequence.order

/-!
# Generalized Beklemishev normal forms

The normal forms `NF A n` (split at the least letter, recursively), their
well-foundedness for well-founded alphabets, and their closure properties.
-/

set_option linter.unusedSectionVars false

instance (A : Type) [LT A] [DecidableLT A] : Min A where
  min a b := if a < b then a else b

def splitOn (A : Type) [DecidableEq A] (a : A) : List A → List (List A)
  | [] => [[]]
  | x :: xs =>
    if x = a then [] :: splitOn A a xs
    else
      match splitOn A a xs with
      | [] => [[x]]
      | y :: ys => (x :: y) :: ys

/-- Split a list at every occurrence of its minimum. -/
def List.md (A : Type) [DecidableEq A] [Min A] (seq : List A) : List (List A) :=
  match seq.min? with
  | none => []
  | some mini => seq.splitOn mini

inductive NFClosed (A : Type) [DecidableEq A] [Min A]
    (P : List (List A) → Prop) : List A → Prop where
  | mk (xs : List A) (h₁ : P (List.md A xs)) (h₂ : ∀ ys ∈ List.md A xs, NFClosed A P ys) :
      NFClosed A P xs

/-- The generalized Beklemishev normal forms of level `n`. -/
def NF (A : Type) [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A]
    (n : Nat) (xs : List A) : Prop :=
  match n with
  | 0 => xs.Pairwise (fun x y => y < x ∨ y = x)
  | m + 1 => NFClosed A (fun ys => NF (List A) m ys) xs

def generalizedBeklemishevConjecture : Prop :=
  ∀ (A : Type) [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A],
    WellFounded (fun x y : A => x < y) →
    ∀ n : Nat, WellFounded (fun x y : {xs : List A // NF A n xs} => x.val < y.val)

/-!
# Basic facts about `List.md` and `NF`

`List.md A xs` splits `xs` at every occurrence of its minimum.  We give a
choice-free description of it (`sepPieces`) and prove the lexicographic
correspondence between a list and its pieces.
-/

open strict_partial_order strict_linear_order

namespace GenBek

section
variable {A : Type} [LT A] [strict_linear_order A]

/-- `a ≤ b`, spelled out. -/
def Le (a b : A) : Prop := a < b ∨ a = b

theorem Le.refl (a : A) : Le a a := Or.inr rfl

theorem Le.trans {a b c : A} (h₁ : Le a b) (h₂ : Le b c) : Le a c := by
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · exact Or.inl (strict_partial_order.trans _ _ _ h₁ h₂)
    · exact Or.inl h₁
  · exact h₂

theorem lt_of_lt_of_Le {a b c : A} (h₁ : a < b) (h₂ : Le b c) : a < c := by
  rcases h₂ with h₂ | rfl
  · exact strict_partial_order.trans _ _ _ h₁ h₂
  · exact h₁

theorem lt_of_Le_of_lt {a b c : A} (h₁ : Le a b) (h₂ : b < c) : a < c := by
  rcases h₁ with h₁ | rfl
  · exact strict_partial_order.trans _ _ _ h₁ h₂
  · exact h₂

theorem not_lt_of_Le {a b : A} (h : Le a b) : ¬ b < a := by
  intro h'
  rcases h with h | rfl
  · exact irrefl _ (strict_partial_order.trans _ _ _ h h')
  · exact irrefl _ h'

theorem Le_of_not_lt {a b : A} (h : ¬ b < a) : Le a b := by
  rcases total a b with h' | h' | h'
  · exact Or.inl h'
  · exact absurd h' h
  · exact Or.inr h'

theorem ne_of_lt' {a b : A} (h : a < b) : a ≠ b := by
  intro e; subst e; exact irrefl _ h

/-! ### Lexicographic order on lists -/

theorem list_lt_irrefl' (xs : List A) : ¬ xs < xs :=
  List.lex_irrefl (fun a h => irrefl a h) xs

theorem list_lt_trans' {xs ys zs : List A} (h₁ : xs < ys) (h₂ : ys < zs) : xs < zs :=
  List.lex_trans (fun h h' => strict_partial_order.trans _ _ _ h h') h₁ h₂

theorem list_prefix_lt' (l : List A) (a : A) (r : List A) : l < l ++ a :: r := by
  induction l with
  | nil => exact List.Lex.nil
  | cons x l ih => exact List.Lex.cons ih

theorem list_append_lt_left (l : List A) {xs ys : List A} (h : xs < ys) : l ++ xs < l ++ ys := by
  induction l with
  | nil => exact h
  | cons a l ih => exact List.Lex.cons ih

/-! ### Splitting at a separator -/

def consHd (x : A) : List (List A) → List (List A)
  | [] => [[x]]
  | p :: ps => (x :: p) :: ps

variable [DecidableEq A]

def sepPieces (μ : A) : List A → List (List A)
  | [] => [[]]
  | x :: xs => if x = μ then [] :: sepPieces μ xs else consHd x (sepPieces μ xs)

def joinTailS (μ : A) : List (List A) → List A
  | [] => []
  | p :: ps => μ :: (p ++ joinTailS μ ps)

def joinS (μ : A) : List (List A) → List A
  | [] => []
  | p :: ps => p ++ joinTailS μ ps

theorem sepPieces_ne_nil (μ : A) (xs : List A) : sepPieces μ xs ≠ [] := by
  cases xs with
  | nil => simp [sepPieces]
  | cons x xs =>
      simp only [sepPieces]
      split
      · simp
      · cases sepPieces μ xs <;> simp [consHd]

theorem splitOnPPrepend_eq (μ : A) : ∀ (xs acc : List A),
    List.splitOnPPrepend (fun x => x == μ) xs acc =
      match sepPieces μ xs with
      | [] => []
      | q :: qs => (acc.reverse ++ q) :: qs
  | [], acc => by simp [List.splitOnPPrepend, sepPieces]
  | x :: xs, acc => by
      simp only [List.splitOnPPrepend, sepPieces]
      by_cases hx : x = μ
      · subst hx
        simp only [beq_self_eq_true, ite_true]
        rw [splitOnPPrepend_eq x xs []]
        cases h : sepPieces x xs with
        | nil => exact absurd h (sepPieces_ne_nil x xs)
        | cons q qs => simp
      · have hb : (x == μ) = false := by simp [hx]
        simp only [hb, Bool.false_eq_true, ite_false, hx]
        rw [splitOnPPrepend_eq μ xs (x :: acc)]
        cases h : sepPieces μ xs with
        | nil => exact absurd h (sepPieces_ne_nil μ xs)
        | cons q qs => simp [consHd]

theorem splitOn_eq (μ : A) (xs : List A) : xs.splitOn μ = sepPieces μ xs := by
  show List.splitOnPPrepend (fun x => x == μ) xs [] = _
  rw [splitOnPPrepend_eq]
  cases h : sepPieces μ xs with
  | nil => exact absurd h (sepPieces_ne_nil μ xs)
  | cons q qs => simp

theorem joinS_consHd (x : A) (μ : A) (ps : List (List A)) (h : ps ≠ []) :
    joinS μ (consHd x ps) = x :: joinS μ ps := by
  cases ps with
  | nil => exact absurd rfl h
  | cons p ps => rfl

theorem joinS_sepPieces (μ : A) : ∀ xs : List A, joinS μ (sepPieces μ xs) = xs
  | [] => rfl
  | x :: xs => by
      simp only [sepPieces]
      by_cases hx : x = μ
      · simp only [hx, ite_true]
        have ih := joinS_sepPieces μ xs
        revert ih
        cases h : sepPieces μ xs with
        | nil => exact absurd h (sepPieces_ne_nil μ xs)
        | cons p ps => intro ih; simp only [joinS] at ih; simp [joinS, joinTailS, ih]
      · simp only [hx, ite_false]
        rw [joinS_consHd _ _ _ (sepPieces_ne_nil μ xs), joinS_sepPieces μ xs]

theorem mem_of_mem_sepPieces (μ : A) : ∀ (xs : List A), ∀ p ∈ sepPieces μ xs, ∀ x ∈ p, x ∈ xs ∧ x ≠ μ
  | [], p, hp, x, hx => by
      simp only [sepPieces, List.mem_singleton] at hp; subst hp; cases hx
  | y :: xs, p, hp, x, hx => by
      simp only [sepPieces] at hp
      by_cases hy : y = μ
      · simp only [hy, ite_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · cases hx
        · have := mem_of_mem_sepPieces μ xs p hp x hx
          exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
      · simp only [hy, ite_false] at hp
        have ih := mem_of_mem_sepPieces μ xs
        revert hp ih
        cases sepPieces μ xs with
        | nil =>
            intro hp _
            simp only [consHd, List.mem_singleton] at hp
            subst hp
            simp only [List.mem_singleton] at hx
            subst hx
            exact ⟨List.mem_cons_self, hy⟩
        | cons q qs =>
            intro hp ih
            simp only [consHd, List.mem_cons] at hp
            rcases hp with rfl | hp
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨List.mem_cons_self, hy⟩
              · have := ih q List.mem_cons_self x hx
                exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
            · have := ih p (List.mem_cons_of_mem q hp) x hx
              exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem sepPieces_free (μ : A) : ∀ (p : List A), μ ∉ p → sepPieces μ p = [p]
  | [], _ => rfl
  | x :: p, h => by
      have hx : x ≠ μ := fun e => h (e ▸ List.mem_cons_self)
      have hp : μ ∉ p := fun hm => h (List.mem_cons_of_mem x hm)
      simp only [sepPieces, hx, ite_false, sepPieces_free μ p hp]
      rfl

theorem sepPieces_append_sep (μ : A) : ∀ (p : List A), μ ∉ p → ∀ zs : List A,
    sepPieces μ (p ++ μ :: zs) = p :: sepPieces μ zs
  | [], _, zs => by simp [sepPieces]
  | x :: p, h, zs => by
      have hx : x ≠ μ := fun e => h (e ▸ List.mem_cons_self)
      have hp : μ ∉ p := fun hm => h (List.mem_cons_of_mem x hm)
      simp only [List.cons_append, sepPieces, hx, ite_false, sepPieces_append_sep μ p hp zs]
      rfl

theorem sepPieces_joinS (μ : A) : ∀ (ps : List (List A)), ps ≠ [] → (∀ p ∈ ps, μ ∉ p) →
    sepPieces μ (joinS μ ps) = ps
  | [], h, _ => absurd rfl h
  | [p], _, hp => by
      simp only [joinS, joinTailS, List.append_nil]
      exact sepPieces_free μ p (hp p List.mem_cons_self)
  | p :: q :: ps, _, hp => by
      have h1 : joinS μ (p :: q :: ps) = p ++ μ :: joinS μ (q :: ps) := by
        simp [joinS, joinTailS]
      rw [h1, sepPieces_append_sep μ p (hp p List.mem_cons_self),
        sepPieces_joinS μ (q :: ps) (by simp) (fun r hr => hp r (List.mem_cons_of_mem p hr))]

/-- Every piece is strictly shorter, when the separator occurs. -/
theorem length_lt_of_mem_sepPieces (μ : A) : ∀ (xs : List A), μ ∈ xs →
    ∀ p ∈ sepPieces μ xs, p.length < xs.length
  | [], h, _, _ => absurd h List.not_mem_nil
  | y :: xs, h, p, hp => by
      simp only [sepPieces] at hp
      by_cases hy : y = μ
      · simp only [hy, ite_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · by_cases hm : μ ∈ xs
          · have := length_lt_of_mem_sepPieces μ xs hm p hp
            simp only [List.length_cons]; omega
          · rw [sepPieces_free μ xs hm, List.mem_singleton] at hp
            subst hp; simp
      · simp only [hy, ite_false] at hp
        have hm : μ ∈ xs := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hy
          · exact h
        have ih := length_lt_of_mem_sepPieces μ xs hm
        revert hp ih
        cases hsp : sepPieces μ xs with
        | nil => exact absurd hsp (sepPieces_ne_nil μ xs)
        | cons q qs =>
            intro hp ih
            simp only [consHd, List.mem_cons] at hp
            rcases hp with rfl | hp
            · have := ih q List.mem_cons_self
              simp only [List.length_cons]; omega
            · have := ih p (List.mem_cons_of_mem q hp)
              simp only [List.length_cons]; omega

/-! ### Lexicographic order and pieces -/

/-- All entries are above `μ`. -/
def AboveL (μ : A) (p : List A) : Prop := ∀ x ∈ p, μ < x

/-- Empty, or starting with `μ`. -/
def SepStart (μ : A) (r : List A) : Prop := r = [] ∨ ∃ t, r = μ :: t

theorem SepStart.joinTailS (μ : A) (ps : List (List A)) : SepStart μ (joinTailS μ ps) := by
  cases ps with
  | nil => exact Or.inl rfl
  | cons p ps => exact Or.inr ⟨_, rfl⟩

theorem AboveL.tail {μ x : A} {p : List A} (h : AboveL μ (x :: p)) : AboveL μ p :=
  fun y hy => h y (List.mem_cons_of_mem x hy)

theorem AboveL.head {μ x : A} {p : List A} (h : AboveL μ (x :: p)) : μ < x :=
  h x List.mem_cons_self

theorem above_append_lt_iff {μ : A} : ∀ {p q r r' : List A}, AboveL μ p → AboveL μ q →
    SepStart μ r → SepStart μ r' → (p ++ r < q ++ r' ↔ p < q ∨ (p = q ∧ r < r'))
  | [], [], r, r', _, _, _, _ => by
      simp only [List.nil_append, true_and]
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun h => absurd h (List.not_lex_nil)) id⟩
  | [], b :: q, r, r', _, hq, hr, _ => by
      refine ⟨fun _ => Or.inl List.Lex.nil, fun _ => ?_⟩
      rcases hr with rfl | ⟨t, rfl⟩
      · exact List.Lex.nil
      · exact List.Lex.rel hq.head
  | a :: p, [], r, r', hp, _, _, hr' => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases hr' with rfl | ⟨t, rfl⟩
        · exact absurd h (List.not_lex_nil)
        · cases h with
          | rel h => exact absurd (strict_partial_order.trans _ _ _ hp.head h) (irrefl _)
          | cons h => exact absurd hp.head (irrefl _)
      · rcases h with h | ⟨h, _⟩
        · exact absurd h (List.not_lex_nil)
        · cases h
  | a :: p, b :: q, r, r', hp, hq, hr, hr' => by
      have ih := @above_append_lt_iff μ p q r r' hp.tail hq.tail hr hr'
      constructor
      · intro h
        cases h with
        | rel h => exact Or.inl (List.Lex.rel h)
        | cons h =>
            rcases ih.mp h with h1 | ⟨rfl, h2⟩
            · exact Or.inl (List.Lex.cons h1)
            · exact Or.inr ⟨rfl, h2⟩
      · intro h
        rcases h with h | ⟨h, h'⟩
        · cases h with
          | rel h => exact List.Lex.rel h
          | cons h => exact List.Lex.cons (ih.mpr (Or.inl h))
        · cases h
          exact List.Lex.cons (ih.mpr (Or.inr ⟨rfl, h'⟩))

theorem joinTailS_lt_iff {μ : A} : ∀ {ps qs : List (List A)}, (∀ p ∈ ps, AboveL μ p) →
    (∀ q ∈ qs, AboveL μ q) → (joinTailS μ ps < joinTailS μ qs ↔ ps < qs)
  | [], [], _, _ => ⟨fun h => absurd h (List.not_lex_nil), fun h => absurd h (List.not_lex_nil)⟩
  | [], _ :: _, _, _ => ⟨fun _ => List.Lex.nil, fun _ => List.Lex.nil⟩
  | _ :: _, [], _, _ => ⟨fun h => absurd h (List.not_lex_nil), fun h => absurd h (List.not_lex_nil)⟩
  | p :: ps, q :: qs, hps, hqs => by
      have hp := hps p List.mem_cons_self
      have hq := hqs q List.mem_cons_self
      have ih := @joinTailS_lt_iff μ ps qs (fun r hr => hps r (List.mem_cons_of_mem p hr))
        (fun r hr => hqs r (List.mem_cons_of_mem q hr))
      have key := above_append_lt_iff hp hq (SepStart.joinTailS μ ps) (SepStart.joinTailS μ qs)
      show List.Lex _ (μ :: (p ++ joinTailS μ ps)) (μ :: (q ++ joinTailS μ qs)) ↔
        List.Lex _ (p :: ps) (q :: qs)
      constructor
      · intro h
        cases h with
        | rel h => exact absurd h (irrefl _)
        | cons h =>
            rcases key.mp h with h1 | ⟨rfl, h2⟩
            · exact List.Lex.rel h1
            · exact List.Lex.cons (ih.mp h2)
      · intro h
        apply List.Lex.cons
        cases h with
        | rel h => exact key.mpr (Or.inl h)
        | cons h => exact key.mpr (Or.inr ⟨rfl, ih.mpr h⟩)

theorem joinS_lt_iff {μ : A} {ps qs : List (List A)} (hps : ps ≠ []) (hqs : qs ≠ [])
    (hp : ∀ p ∈ ps, AboveL μ p) (hq : ∀ q ∈ qs, AboveL μ q) : joinS μ ps < joinS μ qs ↔ ps < qs := by
  cases ps with
  | nil => exact absurd rfl hps
  | cons p ps =>
      cases qs with
      | nil => exact absurd rfl hqs
      | cons q qs =>
          have hp0 := hp p List.mem_cons_self
          have hq0 := hq q List.mem_cons_self
          have ih := @joinTailS_lt_iff _ _ _ _ μ ps qs (fun r hr => hp r (List.mem_cons_of_mem p hr))
            (fun r hr => hq r (List.mem_cons_of_mem q hr))
          show p ++ joinTailS μ ps < q ++ joinTailS μ qs ↔ List.Lex _ (p :: ps) (q :: qs)
          rw [above_append_lt_iff hp0 hq0 (SepStart.joinTailS μ ps) (SepStart.joinTailS μ qs), ih]
          constructor
          · rintro (h | ⟨rfl, h⟩)
            · exact List.Lex.rel h
            · exact List.Lex.cons h
          · intro h
            cases h with
            | rel h => exact Or.inl h
            | cons h => exact Or.inr ⟨rfl, h⟩

/-- Every entry is at least `μ`. -/
def AllGe (μ : A) (xs : List A) : Prop := ∀ x ∈ xs, Le μ x

theorem above_of_mem_sepPieces {μ : A} {xs : List A} (h : AllGe μ xs) :
    ∀ p ∈ sepPieces μ xs, AboveL μ p := by
  intro p hp x hx
  have := mem_of_mem_sepPieces μ xs p hp x hx
  rcases h x this.1 with h' | h'
  · exact h'
  · exact absurd h'.symm this.2

theorem sepPieces_lt_iff {μ : A} {xs ys : List A} (hx : AllGe μ xs) (hy : AllGe μ ys) :
    xs < ys ↔ sepPieces μ xs < sepPieces μ ys := by
  have h := joinS_lt_iff (sepPieces_ne_nil μ xs) (sepPieces_ne_nil μ ys)
    (above_of_mem_sepPieces hx) (above_of_mem_sepPieces hy)
  rw [joinS_sepPieces, joinS_sepPieces] at h
  exact h

/-! ### The minimum and `md` -/

variable [DecidableLT A]

theorem foldl_min_spec : ∀ (as : List A) (a : A),
    (as.foldl min a = a ∨ as.foldl min a ∈ as) ∧ Le (as.foldl min a) a ∧
      ∀ x ∈ as, Le (as.foldl min a) x
  | [], a => ⟨Or.inl rfl, Le.refl a, fun _ h => absurd h List.not_mem_nil⟩
  | b :: bs, a => by
      simp only [List.foldl_cons]
      have ih := foldl_min_spec bs (min a b)
      have hmin : min a b = if a < b then a else b := rfl
      have hab : Le (min a b) a ∧ Le (min a b) b ∧ (min a b = a ∨ min a b = b) := by
        rw [hmin]
        split
        · rename_i h; exact ⟨Le.refl a, Or.inl h, Or.inl rfl⟩
        · rename_i h; exact ⟨Le_of_not_lt h, Le.refl b, Or.inr rfl⟩
      refine ⟨?_, Le.trans ih.2.1 hab.1, ?_⟩
      · rcases ih.1 with h | h
        · rcases hab.2.2 with h' | h'
          · exact Or.inl (h.trans h')
          · rw [h, h']; exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem b h)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Le.trans ih.2.1 hab.2.1
        · exact ih.2.2 x hx

theorem min?_spec {xs : List A} {μ : A} (h : xs.min? = some μ) : μ ∈ xs ∧ AllGe μ xs := by
  cases xs with
  | nil => cases h
  | cons a as =>
      have h' : as.foldl min a = μ := Option.some.inj h
      have hs := foldl_min_spec as a
      rw [h'] at hs
      refine ⟨?_, ?_⟩
      · rcases hs.1 with e | e
        · rw [e]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem a e
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs.2.1
        · exact hs.2.2 x hx

theorem min?_isSome {xs : List A} (h : xs ≠ []) : ∃ μ, xs.min? = some μ := by
  cases xs with
  | nil => exact absurd rfl h
  | cons a as => exact ⟨_, rfl⟩

theorem md_nil : List.md A [] = [] := rfl

theorem md_eq {xs : List A} {μ : A} (h : xs.min? = some μ) : List.md A xs = sepPieces μ xs := by
  unfold List.md
  rw [h]
  exact splitOn_eq μ xs

/-- The minimum of a nonempty list. -/
theorem min_unique {xs : List A} {μ ν : A} (hμ : μ ∈ xs) (hμ' : AllGe μ xs) (hν : ν ∈ xs)
    (hν' : AllGe ν xs) : μ = ν := by
  rcases hμ' ν hν with h | h
  · rcases hν' μ hμ with h' | h'
    · exact absurd (strict_partial_order.trans _ _ _ h h') (irrefl _)
    · exact h'.symm
  · exact h

end

/-!
## Well-foundedness of the generalized Beklemishev normal forms

We prove `generalizedBeklemishevConjecture`: for every well-founded strict linear
order `A` and every `n`, the lexicographic order on `{xs // NF A n xs}` is
well-founded.  The proof is by induction on `n` over all alphabets; the step
uses the accessible part, the minimum letter and the pieces of `List.md`.
No choice principle is used.
-/

section
variable {A : Type} [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A]

theorem NF_succ_iff (n : Nat) (xs : List A) :
    NF A (n + 1) xs ↔ NF (List A) n (List.md A xs) ∧ ∀ ys ∈ List.md A xs, NF A (n + 1) ys := by
  constructor
  · intro h
    cases h with
    | mk _ h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact NFClosed.mk xs h1 h2

theorem mem_joinS {μ x : A} : ∀ {ps : List (List A)}, x ∈ joinS μ ps → x ≠ μ → ∃ p ∈ ps, x ∈ p
  | [], h, _ => absurd h List.not_mem_nil
  | p :: ps, h, hx => by
      simp only [joinS] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨p, List.mem_cons_self, h⟩
      · cases ps with
        | nil => exact absurd h List.not_mem_nil
        | cons q qs =>
            simp only [joinTailS, List.mem_cons] at h
            rcases h with h | h
            · exact absurd h hx
            · obtain ⟨r, hr, hxr⟩ := mem_joinS (ps := q :: qs) (by simpa [joinS] using h) hx
              exact ⟨r, List.mem_cons_of_mem p hr, hxr⟩

theorem mem_sepPieces_of_mem {μ x : A} {xs : List A} (h : x ∈ xs) (hx : x ≠ μ) :
    ∃ p ∈ sepPieces μ xs, x ∈ p := by
  rw [← joinS_sepPieces μ xs] at h
  exact mem_joinS h hx

/-- The first piece, followed by the separator, is a prefix. -/
theorem first_piece_prefix {μ : A} {xs : List A} (hμ : μ ∈ xs) {q : List A}
    {qs : List (List A)} (h : sepPieces μ xs = q :: qs) : ∃ rest, xs = q ++ μ :: rest := by
  have hj := joinS_sepPieces μ xs
  rw [h] at hj
  cases qs with
  | nil =>
      simp only [joinS, joinTailS, List.append_nil] at hj
      have : ∀ y ∈ q, y ≠ μ := fun y hy =>
        (mem_of_mem_sepPieces μ xs q (by rw [h]; exact List.mem_cons_self) y hy).2
      rw [← hj] at hμ
      exact absurd rfl (this μ hμ)
  | cons r rs => exact ⟨r ++ joinTailS μ rs, by rw [← hj]; simp [joinS, joinTailS]⟩

theorem lt_of_first_piece {μ : A} {xs : List A} (hμ : μ ∈ xs) {q : List A}
    {qs : List (List A)} (h : sepPieces μ xs = q :: qs) : q < xs := by
  obtain ⟨rest, e⟩ := first_piece_prefix hμ h
  rw [e]
  exact list_prefix_lt' q μ rest

/-- A list above the separator that is below `xs` is at most the first piece. -/
theorem le_first_piece {μ : A} {xs ys : List A} (hμ : μ ∈ xs) (hall : AllGe μ xs) {q : List A}
    {qs : List (List A)} (h : sepPieces μ xs = q :: qs) (hy : AboveL μ ys) (hlt : ys < xs) :
    Le ys q := by
  obtain ⟨rest, e⟩ := first_piece_prefix hμ h
  have hq : AboveL μ q := above_of_mem_sepPieces hall q (by rw [h]; exact List.mem_cons_self)
  rw [e] at hlt
  have key := above_append_lt_iff (r := []) (r' := μ :: rest) hy hq (Or.inl rfl) (Or.inr ⟨_, rfl⟩)
  rw [List.append_nil] at key
  rcases key.mp hlt with h' | ⟨h', _⟩
  · exact Or.inl h'
  · exact Or.inr h'

end

/-- The first entry of a normal form is its maximum. -/
theorem NF_head_max (n : Nat) : ∀ {A : Type} [LT A] [strict_linear_order A] [DecidableEq A]
    [DecidableLT A] (a : A) (xs : List A), NF A n (a :: xs) → ∀ x ∈ a :: xs, Le x a := by
  induction n with
  | zero =>
      intro A _ _ _ _ a xs h x hx
      have h' : List.Pairwise (fun x y : A => y < x ∨ y = x) (a :: xs) := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Le.refl _
      · exact (List.pairwise_cons.mp h').1 x hx
  | succ n ih =>
      intro A _ _ _ _
      -- strong induction on the length
      suffices H : ∀ k, ∀ (a : A) (xs : List A), xs.length ≤ k → NF A (n + 1) (a :: xs) →
          ∀ x ∈ a :: xs, Le x a by
        intro a xs h x hx
        exact H xs.length a xs (Nat.le_refl _) h x hx
      intro k
      induction k with
      | zero =>
          intro a xs hk _ x hx
          have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst this
          rw [List.mem_singleton.mp hx]
          exact Le.refl _
      | succ k ihk =>
          intro a xs hk h x hx
          obtain ⟨μ, hm⟩ := min?_isSome (List.cons_ne_nil a xs)
          have hspec := min?_spec hm
          have hnf := (NF_succ_iff n (a :: xs)).mp h
          rw [md_eq hm] at hnf
          by_cases ha : a = μ
          · subst ha
            have hsp : sepPieces a (a :: xs) = [] :: sepPieces a xs := by simp [sepPieces]
            rw [hsp] at hnf
            have hmax := ih ([] : List A) (sepPieces a xs) hnf.1
            by_cases hxa : x = a
            · rw [hxa]; exact Le.refl _
            · obtain ⟨p, hp, hxp⟩ := mem_sepPieces_of_mem hx hxa
              rw [hsp] at hp
              rcases hmax p hp with h' | h'
              · exact absurd h' List.not_lex_nil
              · subst h'; cases hxp
          · have hsp : sepPieces μ (a :: xs) = consHd a (sepPieces μ xs) := by simp [sepPieces, ha]
            rw [hsp] at hnf
            cases hq : sepPieces μ xs with
            | nil => exact absurd hq (sepPieces_ne_nil μ xs)
            | cons q qs =>
                rw [hq] at hnf hsp
                have hmax := ih (a :: q) qs hnf.1
                by_cases hxμ : x = μ
                · rw [hxμ]; exact hspec.2 a List.mem_cons_self
                · obtain ⟨p, hp, hxp⟩ := mem_sepPieces_of_mem hx hxμ
                  rw [hsp] at hp
                  cases p with
                  | nil => cases hxp
                  | cons b p' =>
                      have hpnf := hnf.2 _ hp
                      have hlen := length_lt_of_mem_sepPieces μ (a :: xs) hspec.1 (b :: p')
                        (by rw [hsp]; exact hp)
                      have hxb := ihk b p' (by simp only [List.length_cons] at hlen hk; omega)
                        hpnf x hxp
                      have hba : Le b a := by
                        rcases hmax _ hp with h' | h'
                        · cases h' with
                          | rel h' => exact Or.inl h'
                          | cons h' => exact Or.inr rfl
                        · cases h'; exact Or.inr rfl
                      exact Le.trans hxb hba

/-! ### The base case: non-increasing lists -/

section
variable {A : Type} [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A]

theorem acc_of_nil {P : List A → Prop} {x : {xs : List A // P xs}} (h : x.1 = []) :
    Acc (fun x y : {xs : List A // P xs} => x.1 < y.1) x := by
  constructor
  intro y hy
  rw [h] at hy
  exact absurd hy List.not_lex_nil

theorem wf_zero (S : A → Prop) (hS : WellFounded (fun a b : {a // S a} => a.1 < b.1)) :
    WellFounded (fun x y : {xs : List A // NF A 0 xs ∧ ∀ a ∈ xs, S a} => x.1 < y.1) := by
  let X := {xs : List A // NF A 0 xs ∧ ∀ a ∈ xs, S a}
  let R := fun x y : X => x.1 < y.1
  have tailX : ∀ (a : A) (rest : List A), NF A 0 (a :: rest) ∧ (∀ b ∈ a :: rest, S b) →
      NF A 0 rest ∧ ∀ b ∈ rest, S b := by
    intro a rest h
    exact ⟨(List.pairwise_cons.mp h.1).2, fun b hb => h.2 b (List.mem_cons_of_mem a hb)⟩
  have claim : ∀ a : {a // S a}, ∀ x : X, (∃ rest, x.1 = a.1 :: rest) → Acc R x := by
    intro a
    induction a using hS.induction with
    | h a iha =>
        -- adding the head `a` preserves accessibility
        have cons_acc : ∀ rest : X, Acc R rest → ∀ h : NF A 0 (a.1 :: rest.1) ∧
            ∀ b ∈ a.1 :: rest.1, S b, Acc R ⟨a.1 :: rest.1, h⟩ := by
          intro rest hr
          induction hr with
          | intro rest _ ihr =>
              intro h
              constructor
              intro y hy
              cases hy0 : y.1 with
              | nil => exact acc_of_nil hy0
              | cons b ys =>
                  have hy' : b :: ys < a.1 :: rest.1 := hy0 ▸ hy
                  cases hy' with
                  | rel hb =>
                      exact iha ⟨b, y.2.2 b (by rw [hy0]; exact List.mem_cons_self)⟩ hb y ⟨ys, hy0⟩
                  | cons hys =>
                      have hyX := y.2
                      rw [hy0] at hyX
                      have hys' := ihr ⟨ys, tailX _ _ hyX⟩ hys hyX
                      have : y = ⟨a.1 :: ys, hyX⟩ := Subtype.ext hy0
                      rw [this]; exact hys'
        intro x hx
        obtain ⟨rest, hrest⟩ := hx
        -- strong induction on the length of `rest`
        suffices H : ∀ k, ∀ rest : List A, rest.length ≤ k → ∀ h : NF A 0 (a.1 :: rest) ∧
            ∀ b ∈ a.1 :: rest, S b, Acc R ⟨a.1 :: rest, h⟩ by
          have hx := x.2
          rw [hrest] at hx
          have : x = ⟨a.1 :: rest, hx⟩ := Subtype.ext hrest
          rw [this]; exact H rest.length rest (Nat.le_refl _) hx
        intro k
        induction k with
        | zero =>
            intro rest hk h
            have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst this
            exact cons_acc ⟨[], tailX _ _ h⟩ (acc_of_nil rfl) h
        | succ k ihk =>
            intro rest hk h
            apply cons_acc ⟨rest, tailX _ _ h⟩ _ h
            cases rest with
            | nil => exact acc_of_nil rfl
            | cons b rest' =>
                have hba : b < a.1 ∨ b = a.1 := (List.pairwise_cons.mp h.1).1 b List.mem_cons_self
                rcases hba with hba | rfl
                · exact iha ⟨b, h.2 b (List.mem_cons_of_mem _ List.mem_cons_self)⟩ hba _ ⟨rest', rfl⟩
                · exact ihk rest' (by simp only [List.length_cons] at hk; omega) _
  constructor
  intro x
  cases hx : x.1 with
  | nil => exact acc_of_nil hx
  | cons a rest => exact claim ⟨a, x.2.2 a (by rw [hx]; exact List.mem_cons_self)⟩ x ⟨rest, hx⟩

end

/-! ### The induction step -/

theorem wf_succ (n : Nat)
    (IH : ∀ {B : Type} [LT B] [strict_linear_order B] [DecidableEq B] [DecidableLT B]
      (S : B → Prop), WellFounded (fun a b : {a // S a} => a.1 < b.1) →
      WellFounded (fun x y : {xs : List B // NF B n xs ∧ ∀ a ∈ xs, S a} => x.1 < y.1))
    {A : Type} [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A]
    (S : A → Prop) (hS : WellFounded (fun a b : {a // S a} => a.1 < b.1)) :
    WellFounded (fun x y : {xs : List A // NF A (n + 1) xs ∧ ∀ a ∈ xs, S a} => x.1 < y.1) := by
  let X := {xs : List A // NF A (n + 1) xs ∧ ∀ a ∈ xs, S a}
  let R := fun x y : X => x.1 < y.1
  let Gl : List A → Prop := fun ys => ∃ h : NF A (n + 1) ys ∧ ∀ a ∈ ys, S a, Acc R ⟨ys, h⟩
  have Gl_down : ∀ p q : List A, Gl q → (NF A (n + 1) p ∧ ∀ a ∈ p, S a) → Le p q → Gl p := by
    intro p q hq hp hle
    obtain ⟨hq', acc⟩ := hq
    refine ⟨hp, ?_⟩
    rcases hle with hle | rfl
    · exact acc.inv (show (⟨p, hp⟩ : X).1 < (⟨q, hq'⟩ : X).1 from hle)
    · exact acc
  have hG : WellFounded (fun a b : {ys // Gl ys} => a.1 < b.1) := by
    have key : ∀ x : X, Acc R x → ∀ hg : Gl x.1,
        Acc (fun a b : {ys // Gl ys} => a.1 < b.1) ⟨x.1, hg⟩ := by
      intro x hx
      induction hx with
      | intro x _ ih =>
          intro hg
          constructor
          intro z hz
          obtain ⟨hz1, hz2⟩ := z.2
          exact ih ⟨z.1, hz1⟩ hz z.2
    constructor
    intro y
    obtain ⟨ys, hy⟩ := y
    obtain ⟨h, acc⟩ := hy
    exact key ⟨ys, h⟩ acc ⟨h, acc⟩
  have hY := IH (B := List A) Gl hG
  have pieceX : ∀ x : X, ∀ μ, x.1.min? = some μ → ∀ p ∈ sepPieces μ x.1,
      NF A (n + 1) p ∧ ∀ a ∈ p, S a := by
    intro x μ hm p hp
    have hnf := (NF_succ_iff n x.1).mp x.2.1
    rw [md_eq hm] at hnf
    exact ⟨hnf.2 p hp, fun a ha => x.2.2 a (mem_of_mem_sepPieces μ x.1 p hp a ha).1⟩
  have firstMax : ∀ y : X, ∀ ν, y.1.min? = some ν → ∀ Q0 Qs, sepPieces ν y.1 = Q0 :: Qs →
      ∀ Q ∈ Q0 :: Qs, Le Q Q0 := by
    intro y ν hν Q0 Qs hq Q hQ
    have hnf := (NF_succ_iff n y.1).mp y.2.1
    rw [md_eq hν, hq] at hnf
    exact NF_head_max n Q0 Qs hnf.1 Q hQ
  have claim : ∀ μ : {a // S a}, ∀ x : X, x.1.min? = some μ.1 →
      (∀ p ∈ sepPieces μ.1 x.1, Gl p) → Acc R x := by
    intro μ
    induction μ using hS.induction with
    | h μ ihμ =>
        have main : ∀ L : {Ls : List (List A) // NF (List A) n Ls ∧ ∀ ys ∈ Ls, Gl ys},
            ∀ x : X, x.1.min? = some μ.1 → sepPieces μ.1 x.1 = L.1 → Acc R x := by
          intro L
          induction L using hY.induction with
          | h L ihL =>
              intro x hmin hsp
              have hspec := min?_spec hmin
              cases hP : sepPieces μ.1 x.1 with
              | nil => exact absurd hP (sepPieces_ne_nil _ _)
              | cons P0 Ps =>
                  have hP0 : Gl P0 := L.2.2 P0 (by rw [← hsp, hP]; exact List.mem_cons_self)
                  have sameMin : ∀ y : X, y.1 < x.1 → y.1.min? = some μ.1 → Acc R y := by
                    intro y hy hymin
                    have hyspec := min?_spec hymin
                    have hlt : sepPieces μ.1 y.1 < sepPieces μ.1 x.1 :=
                      (sepPieces_lt_iff hyspec.2 hspec.2).mp hy
                    have hnfy := (NF_succ_iff n y.1).mp y.2.1
                    rw [md_eq hymin] at hnfy
                    cases hQ : sepPieces μ.1 y.1 with
                    | nil => exact absurd hQ (sepPieces_ne_nil _ _)
                    | cons Q0 Qs =>
                        rw [hQ, hP] at hlt
                        have hQ0P0 : Le Q0 P0 := by
                          cases hlt with
                          | rel h => exact Or.inl h
                          | cons h => exact Or.inr rfl
                        have hall : ∀ Q ∈ Q0 :: Qs, Gl Q := fun Q hQm =>
                          Gl_down Q P0 hP0 (pieceX y μ.1 hymin Q (by rw [hQ]; exact hQm))
                            (Le.trans (firstMax y μ.1 hymin Q0 Qs hQ Q hQm) hQ0P0)
                        rw [hQ] at hnfy
                        refine ihL ⟨Q0 :: Qs, hnfy.1, hall⟩ ?_ y hymin hQ
                        show Q0 :: Qs < L.1
                        rw [← hsp, hP]; exact hlt
                  have aboveMin : ∀ y : X, y.1 < x.1 → AboveL μ.1 y.1 → Acc R y := by
                    intro y hy hab
                    have hle := le_first_piece hspec.1 hspec.2 hP hab hy
                    obtain ⟨_, acc⟩ := Gl_down y.1 P0 hP0 y.2 hle
                    exact acc
                  have lowerMin : ∀ k, ∀ y : X, y.1.length ≤ k → y.1 < x.1 → ∀ ν,
                      y.1.min? = some ν → ν < μ.1 → Acc R y := by
                    intro k
                    induction k with
                    | zero =>
                        intro y hk _ ν hν _
                        have : y.1 = [] := List.eq_nil_of_length_eq_zero (by omega)
                        rw [this] at hν; cases hν
                    | succ k ihk =>
                        intro y hk hy ν hν hνμ
                        have hyspec := min?_spec hν
                        cases hQ : sepPieces ν y.1 with
                        | nil => exact absurd hQ (sepPieces_ne_nil _ _)
                        | cons Q0 Qs =>
                            have hQ0lt : Q0 < y.1 := lt_of_first_piece hyspec.1 hQ
                            have hQ0x : Q0 < x.1 := list_lt_trans' hQ0lt hy
                            have hQ0X := pieceX y ν hν Q0 (by rw [hQ]; exact List.mem_cons_self)
                            have hlen : Q0.length < y.1.length := by
                              obtain ⟨rest, e⟩ := first_piece_prefix hyspec.1 hQ
                              rw [e]; simp
                            have accLower : ∀ z : X, z.1 < x.1 → z.1.length < y.1.length →
                                Acc R z := by
                              intro z hz hzlen
                              cases hz0 : z.1 with
                              | nil => exact acc_of_nil hz0
                              | cons c cs =>
                                  obtain ⟨ρ, hρ⟩ := min?_isSome (List.cons_ne_nil c cs)
                                  rw [← hz0] at hρ
                                  rcases total ρ μ.1 with h | h | h
                                  · exact ihk z (by omega) hz ρ hρ h
                                  · have hab : AboveL μ.1 z.1 := by
                                      intro w hw
                                      exact lt_of_lt_of_Le h ((min?_spec hρ).2 w hw)
                                    exact aboveMin z hz hab
                                  · rw [h] at hρ
                                    exact sameMin z hz hρ
                            have hGQ0 : Gl Q0 := ⟨hQ0X, accLower ⟨Q0, hQ0X⟩ hQ0x hlen⟩
                            have hall : ∀ Q ∈ sepPieces ν y.1, Gl Q := by
                              rw [hQ]
                              intro Q hQm
                              exact Gl_down Q Q0 hGQ0 (pieceX y ν hν Q (by rw [hQ]; exact hQm))
                                (firstMax y ν hν Q0 Qs hQ Q hQm)
                            exact ihμ ⟨ν, y.2.2 ν hyspec.1⟩ hνμ y hν hall
                  constructor
                  intro y hy
                  cases hy0 : y.1 with
                  | nil => exact acc_of_nil hy0
                  | cons b ys =>
                      obtain ⟨ν, hν⟩ := min?_isSome (List.cons_ne_nil b ys)
                      rw [← hy0] at hν
                      rcases total ν μ.1 with h | h | h
                      · exact lowerMin _ y (Nat.le_refl _) hy ν hν h
                      · have hab : AboveL μ.1 y.1 := by
                          intro z hz
                          exact lt_of_lt_of_Le h ((min?_spec hν).2 z hz)
                        exact aboveMin y hy hab
                      · rw [h] at hν
                        exact sameMin y hy hν
        intro x hmin hpieces
        have hnf := (NF_succ_iff n x.1).mp x.2.1
        rw [md_eq hmin] at hnf
        exact main ⟨sepPieces μ.1 x.1, hnf.1, hpieces⟩ x hmin rfl
  constructor
  intro x
  suffices H : ∀ k, ∀ x : X, x.1.length ≤ k → Acc R x from H _ x (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
      intro x hk
      exact acc_of_nil (List.eq_nil_of_length_eq_zero (by omega))
  | succ k ihk =>
      intro x hk
      cases hx : x.1 with
      | nil => exact acc_of_nil hx
      | cons b xs =>
          obtain ⟨μ, hμ⟩ := min?_isSome (List.cons_ne_nil b xs)
          rw [← hx] at hμ
          have hspec := min?_spec hμ
          apply claim ⟨μ, x.2.2 μ hspec.1⟩ x hμ
          intro p hp
          have hpX := pieceX x μ hμ p hp
          have hlen := length_lt_of_mem_sepPieces μ x.1 hspec.1 p hp
          exact ⟨hpX, ihk ⟨p, hpX⟩ (by simp only; omega)⟩

theorem nf_wf (n : Nat) : ∀ {A : Type} [LT A] [strict_linear_order A] [DecidableEq A]
    [DecidableLT A] (S : A → Prop), WellFounded (fun a b : {a // S a} => a.1 < b.1) →
    WellFounded (fun x y : {xs : List A // NF A n xs ∧ ∀ a ∈ xs, S a} => x.1 < y.1) := by
  induction n with
  | zero => intro A _ _ _ _ S hS; exact wf_zero S hS
  | succ n ih => intro A _ _ _ _ S hS; exact wf_succ n ih S hS

end GenBek

/-- The generalized Beklemishev conjecture holds. -/
theorem generalizedBeklemishev : generalizedBeklemishevConjecture := by
  intro A _ _ _ _ hA n
  have hS : WellFounded (fun a b : {a : A // True} => a.1 < b.1) :=
    InvImage.wf (fun a : {a : A // True} => a.1) hA
  have h := GenBek.nf_wf n (fun _ : A => True) hS
  have hInv := InvImage.wf
    (fun x : {xs : List A // NF A n xs} =>
      (⟨x.1, x.2, fun _ _ => trivial⟩ : {xs : List A // NF A n xs ∧ ∀ a ∈ xs, True})) h
  exact hInv

open GenBek

namespace Mbek

/-!
## Closure properties of the normal forms `NF A n`
-/

section
variable {B : Type} [LT B] [strict_linear_order B] [DecidableEq B] [DecidableLT B]

theorem joinTailS_append (μ : B) (P Q : List (List B)) :
    joinTailS μ (P ++ Q) = joinTailS μ P ++ joinTailS μ Q := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [joinTailS, ih]

theorem joinS_append (μ : B) (P Q : List (List B)) (hP : P ≠ []) (hQ : Q ≠ []) :
    joinS μ (P ++ Q) = joinS μ P ++ μ :: joinS μ Q := by
  cases P with
  | nil => exact absurd rfl hP
  | cons a P =>
      cases Q with
      | nil => exact absurd rfl hQ
      | cons b Q => simp [joinS, joinTailS_append, joinTailS]

theorem min?_eq_of {L : List B} {ν : B} (hν : ν ∈ L) (hall : AllGe ν L) : L.min? = some ν := by
  obtain ⟨μ, hμ⟩ := min?_isSome (List.ne_nil_of_mem hν)
  have hs := min?_spec hμ
  rw [hμ, min_unique hs.1 hs.2 hν hall]

theorem md_of_min {L : List B} {ν : B} (hν : ν ∈ L) (hall : AllGe ν L) :
    List.md B L = sepPieces ν L := md_eq (min?_eq_of hν hall)

theorem nil_Le_list (P : List B) : Le ([] : List B) P := by
  cases P with
  | nil => exact Or.inr rfl
  | cons a P => exact Or.inl List.Lex.nil

theorem joinS_append_last (μ : B) (Ps : List (List B)) (P : List B) (x : B) :
    joinS μ (Ps ++ [P]) ++ [x] = joinS μ (Ps ++ [P ++ [x]]) := by
  cases Ps with
  | nil => simp [joinS, joinTailS]
  | cons Q Qs =>
      rw [joinS_append μ _ _ (List.cons_ne_nil _ _) (by simp),
        joinS_append μ _ _ (List.cons_ne_nil _ _) (by simp)]
      simp [joinS, joinTailS]

theorem sepPieces_snoc_ne (μ : B) (A : List B) (x : B) (hx : x ≠ μ) :
    ∃ Ps P, sepPieces μ A = Ps ++ [P] ∧ sepPieces μ (A ++ [x]) = Ps ++ [P ++ [x]] := by
  rcases List.eq_nil_or_concat (sepPieces μ A) with h | ⟨Ps, P, h⟩
  · exact absurd h (sepPieces_ne_nil μ A)
  · rw [List.concat_eq_append] at h
    refine ⟨Ps, P, h, ?_⟩
    have hA : A = joinS μ (Ps ++ [P]) := by rw [← h, joinS_sepPieces]
    rw [hA, joinS_append_last]
    apply sepPieces_joinS μ _ (by simp)
    intro Q hQ
    rcases List.mem_append.mp hQ with hQ | hQ
    · intro hm
      exact (mem_of_mem_sepPieces μ A Q (by rw [h]; exact List.mem_append_left _ hQ) μ hm).2 rfl
    · rw [List.mem_singleton.mp hQ]
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (mem_of_mem_sepPieces μ A P (by rw [h]; simp) μ hm).2 rfl
      · exact hx (List.mem_singleton.mp hm).symm

theorem sepPieces_snoc_eq (μ : B) (A : List B) :
    sepPieces μ (A ++ [μ]) = sepPieces μ A ++ [[]] := by
  induction A with
  | nil => simp [sepPieces]
  | cons a A ih =>
      simp only [List.cons_append, sepPieces]
      split
      · rw [ih]; rfl
      · rw [ih]
        cases h : sepPieces μ A with
        | nil => exact absurd h (sepPieces_ne_nil μ A)
        | cons q qs => rfl

theorem sepPieces_replicate (a : B) : ∀ j, sepPieces a (List.replicate j a) = List.replicate (j + 1) [] := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, sepPieces, ih]

/-! ### Basic normal forms -/

theorem NF_nil : ∀ (k : Nat) {B : Type} [LT B] [strict_linear_order B] [DecidableEq B]
    [DecidableLT B], NF B k []
  | 0, _, _, _, _, _ => List.Pairwise.nil
  | k + 1, B, _, _, _, _ => by
      rw [NF_succ_iff, md_nil]
      exact ⟨NF_nil k, fun _ h => absurd h List.not_mem_nil⟩

theorem NF_replicate : ∀ (k : Nat) {B : Type} [LT B] [strict_linear_order B] [DecidableEq B]
    [DecidableLT B] (a : B) (j : Nat), NF B k (List.replicate j a)
  | 0, _, _, _, _, _, a, j => List.pairwise_replicate.mpr (Or.inr (Or.inr rfl))
  | k + 1, B, _, _, _, _, a, j => by
      cases j with
      | zero => exact NF_nil (k + 1)
      | succ j =>
          rw [NF_succ_iff, md_of_min (ν := a) (by simp) (by
            intro z hz; rw [(List.mem_replicate.mp hz).2]; exact Le.refl a), sepPieces_replicate]
          refine ⟨NF_replicate k [] (j + 2), ?_⟩
          intro ys hys
          rw [(List.mem_replicate.mp hys).2]
          exact NF_nil (k + 1)

theorem NF_singleton (k : Nat) (a : B) : NF B k [a] := NF_replicate k a 1

/-- Appending an entry below everything keeps the normal form. -/
theorem NF_appmin : ∀ (k : Nat) {B : Type} [LT B] [strict_linear_order B] [DecidableEq B]
    [DecidableLT B] (L : List B) (b : B), NF B k L → (∀ z ∈ L, Le b z) → NF B k (L ++ [b])
  | 0, _, _, _, _, _, L, b, h, hall => by
      show List.Pairwise _ (L ++ [b])
      rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro z hz y hy
      rw [List.mem_singleton.mp hy]
      rcases hall z hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  | k + 1, B, _, _, _, _, L, b, h, hall => by
      cases L with
      | nil => exact NF_singleton (k + 1) b
      | cons c L' =>
          obtain ⟨μ, hμ⟩ := min?_isSome (List.cons_ne_nil c L')
          have hs := min?_spec hμ
          have hnf := (NF_succ_iff k _).mp h
          rw [md_eq hμ] at hnf
          rcases hall μ hs.1 with hbμ | rfl
          · -- the new entry is the strict minimum
            have hbnot : b ∉ c :: L' := by
              intro hb
              exact not_lt_of_Le (hs.2 b hb) hbμ
            have hall' : AllGe b ((c :: L') ++ [b]) := by
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact Or.inl (lt_of_lt_of_Le hbμ (hs.2 z hz))
              · rw [List.mem_singleton.mp hz]; exact Le.refl b
            rw [NF_succ_iff, md_of_min (by simp) hall', sepPieces_snoc_eq,
              sepPieces_free b _ hbnot]
            refine ⟨NF_appmin k [c :: L'] [] (NF_singleton k _) (fun z _ => nil_Le_list z), ?_⟩
            intro ys hys
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton] at hys
            rcases hys with rfl | rfl | h'
            · exact h
            · exact NF_nil (k + 1)
            · cases h'
          · have hall' : AllGe b ((c :: L') ++ [b]) := by
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact hs.2 z hz
              · rw [List.mem_singleton.mp hz]; exact Le.refl b
            rw [NF_succ_iff, md_of_min (by simp) hall', sepPieces_snoc_eq]
            refine ⟨NF_appmin k _ [] hnf.1 (fun z _ => nil_Le_list z), ?_⟩
            intro ys hys
            rcases List.mem_append.mp hys with hys | hys
            · exact hnf.2 ys hys
            · rw [List.mem_singleton.mp hys]; exact NF_nil (k + 1)

/-- Prefixes and decreasing the last entry keep the normal form. -/
theorem NF_prefix_dec : ∀ (k : Nat) {B : Type} [LT B] [strict_linear_order B] [DecidableEq B]
    [DecidableLT B], (∀ (A : List B) (x : B), NF B k (A ++ [x]) → NF B k A) ∧
      (∀ (A : List B) (x y : B), NF B k (A ++ [x]) → y < x → NF B k (A ++ [y]))
  | 0, B, _, _, _, _ => by
      refine ⟨fun A x h => (List.pairwise_append.mp h).1, fun A x y h hyx => ?_⟩
      have h' := List.pairwise_append.mp h
      show List.Pairwise _ (A ++ [y])
      rw [List.pairwise_append]
      refine ⟨h'.1, List.pairwise_singleton _ _, ?_⟩
      intro z hz w hw
      rw [List.mem_singleton.mp hw]
      rcases h'.2.2 z hz x (List.mem_singleton_self x) with h'' | h''
      · exact Or.inl (strict_partial_order.trans _ _ _ hyx h'')
      · rw [← h'']; exact Or.inl hyx
  | k + 1, B, _, _, _, _ => by
      obtain ⟨ihp, ihd⟩ := NF_prefix_dec k (B := List B)
      have hpre : ∀ (n : Nat) (A : List B) (x : B), A.length ≤ n → NF B (k + 1) (A ++ [x]) →
          NF B (k + 1) A := by
        intro n
        induction n with
        | zero =>
            intro A x hA _
            rw [List.eq_nil_of_length_eq_zero (by omega : A.length = 0)]
            exact NF_nil (k + 1)
        | succ n ihn =>
            intro A x hA h
            by_cases hA0 : A = []
            · rw [hA0]; exact NF_nil (k + 1)
            obtain ⟨ν, hν⟩ := min?_isSome hA0
            have hs := min?_spec hν
            obtain ⟨μ, hμ⟩ := min?_isSome (show A ++ [x] ≠ [] by simp)
            have hsL := min?_spec hμ
            have hnf := (NF_succ_iff k (A ++ [x])).mp h
            rw [md_eq hμ] at hnf
            by_cases hxμ : x = μ
            · subst hxμ
              by_cases hxA : x ∈ A
              · have hνx : ν = x := min_unique hs.1 hs.2 hxA
                  (fun z hz => hsL.2 z (List.mem_append_left _ hz))
                subst hνx
                rw [sepPieces_snoc_eq] at hnf
                rw [NF_succ_iff, md_eq hν]
                exact ⟨ihp _ _ hnf.1, fun ys hys => hnf.2 ys (List.mem_append_left _ hys)⟩
              · rw [sepPieces_snoc_eq, sepPieces_free x A hxA] at hnf
                exact hnf.2 A (by simp)
            · have hμA : μ ∈ A := by
                rcases List.mem_append.mp hsL.1 with h' | h'
                · exact h'
                · exact absurd (List.mem_singleton.mp h').symm hxμ
              have hνμ : ν = μ := min_unique hs.1 hs.2 hμA
                (fun z hz => hsL.2 z (List.mem_append_left _ hz))
              subst hνμ
              obtain ⟨Ps, P, hA, hL⟩ := sepPieces_snoc_ne ν A x hxμ
              rw [hL] at hnf
              rw [NF_succ_iff, md_eq hν, hA]
              have hPx : P < P ++ [x] := by simpa using list_prefix_lt' P x []
              refine ⟨ihd Ps (P ++ [x]) P hnf.1 hPx, ?_⟩
              intro ys hys
              rcases List.mem_append.mp hys with hys | hys
              · exact hnf.2 ys (List.mem_append_left _ hys)
              · rw [List.mem_singleton.mp hys]
                have hlen := length_lt_of_mem_sepPieces ν A hs.1 P (by rw [hA]; simp)
                exact ihn P x (by omega) (hnf.2 _ (by simp))
      have hpre' : ∀ (A : List B) (x : B), NF B (k + 1) (A ++ [x]) → NF B (k + 1) A :=
        fun A x h => hpre A.length A x (Nat.le_refl _) h
      have hdec : ∀ (n : Nat) (A : List B) (x y : B), A.length ≤ n → NF B (k + 1) (A ++ [x]) →
          y < x → NF B (k + 1) (A ++ [y]) := by
        intro n
        induction n with
        | zero =>
            intro A x y hA _ _
            rw [List.eq_nil_of_length_eq_zero (by omega : A.length = 0)]
            exact NF_singleton (k + 1) y
        | succ n ihn =>
            intro A x y hA h hyx
            by_cases hA0 : A = []
            · rw [hA0]; exact NF_singleton (k + 1) y
            obtain ⟨ν, hν⟩ := min?_isSome hA0
            have hs := min?_spec hν
            have hpA := hpre' A x h
            have hnfA := (NF_succ_iff k A).mp hpA
            rw [md_eq hν] at hnfA
            rcases total y ν with hyν | hνy | rfl
            · have hynot : y ∉ A := fun hy => not_lt_of_Le (hs.2 y hy) hyν
              have hall : AllGe y (A ++ [y]) := by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact Or.inl (lt_of_lt_of_Le hyν (hs.2 z hz))
                · rw [List.mem_singleton.mp hz]; exact Le.refl y
              rw [NF_succ_iff, md_of_min (by simp) hall, sepPieces_snoc_eq, sepPieces_free y A hynot]
              refine ⟨NF_appmin k [A] [] (NF_singleton k A) (fun z _ => nil_Le_list z), ?_⟩
              intro ys hys
              simp only [List.cons_append, List.nil_append, List.mem_cons] at hys
              rcases hys with rfl | rfl | h'
              · exact hpA
              · exact NF_nil (k + 1)
              · cases h'
            · have hνx : ν < x := strict_partial_order.trans _ _ _ hνy hyx
              have hallx : AllGe ν (A ++ [x]) := by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hs.2 z hz
                · rw [List.mem_singleton.mp hz]; exact Or.inl hνx
              have hally : AllGe ν (A ++ [y]) := by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hs.2 z hz
                · rw [List.mem_singleton.mp hz]; exact Or.inl hνy
              obtain ⟨Ps, P, hA, hLx⟩ := sepPieces_snoc_ne ν A x (fun e => irrefl _ (e ▸ hνx))
              obtain ⟨Ps', P', hA', hLy⟩ := sepPieces_snoc_ne ν A y (fun e => irrefl _ (e ▸ hνy))
              rw [hA] at hA'
              obtain ⟨rfl, hPP⟩ := List.append_inj' hA' rfl
              cases hPP
              have hnf := (NF_succ_iff k (A ++ [x])).mp h
              rw [md_of_min (List.mem_append_left _ hs.1) hallx, hLx] at hnf
              rw [NF_succ_iff, md_of_min (List.mem_append_left _ hs.1) hally, hLy]
              have hlt : P ++ [y] < P ++ [x] := list_append_lt_left P (List.Lex.rel hyx)
              refine ⟨ihd Ps (P ++ [x]) (P ++ [y]) hnf.1 hlt, ?_⟩
              intro ys hys
              rcases List.mem_append.mp hys with hys | hys
              · exact hnf.2 ys (List.mem_append_left _ hys)
              · rw [List.mem_singleton.mp hys]
                have hlen := length_lt_of_mem_sepPieces ν A hs.1 P (by rw [hA]; simp)
                exact ihn P x y (by omega) (hnf.2 _ (by simp)) hyx
            · have hall : AllGe y (A ++ [y]) := by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hs.2 z hz
                · rw [List.mem_singleton.mp hz]; exact Le.refl y
              rw [NF_succ_iff, md_of_min (by simp) hall, sepPieces_snoc_eq]
              refine ⟨NF_appmin k _ [] hnfA.1 (fun z _ => nil_Le_list z), ?_⟩
              intro ys hys
              rcases List.mem_append.mp hys with hys | hys
              · exact hnfA.2 ys hys
              · rw [List.mem_singleton.mp hys]; exact NF_nil (k + 1)
      exact ⟨hpre', fun A x y h hyx => hdec A.length A x y (Nat.le_refl _) h hyx⟩

end

end Mbek

namespace GenBek

/-!
## Normal forms are invariant under order embeddings of the alphabet
-/

section
variable {A B : Type} [LT A] [strict_linear_order A] [DecidableEq A] [DecidableLT A]
  [LT B] [strict_linear_order B] [DecidableEq B] [DecidableLT B]

/-- `f` is strictly monotone on the entries of `xs`. -/
def MonoOn (f : A → B) (xs : List A) : Prop := ∀ x ∈ xs, ∀ y ∈ xs, x < y → f x < f y

theorem MonoOn.le {f : A → B} {xs : List A} (hf : MonoOn f xs) {x y : A} (hx : x ∈ xs)
    (hy : y ∈ xs) (h : Le x y) : Le (f x) (f y) := by
  rcases h with h | rfl
  · exact Or.inl (hf x hx y hy h)
  · exact Le.refl _

theorem MonoOn.inj {f : A → B} {xs : List A} (hf : MonoOn f xs) {x y : A} (hx : x ∈ xs)
    (hy : y ∈ xs) (h : f x = f y) : x = y := by
  rcases strict_linear_order.total x y with h' | h' | h'
  · exact absurd h (ne_of_lt' (hf x hx y hy h'))
  · exact absurd h.symm (ne_of_lt' (hf y hy x hx h'))
  · exact h'

theorem MonoOn.sub {f : A → B} {xs ys : List A} (hf : MonoOn f xs) (h : ∀ y ∈ ys, y ∈ xs) :
    MonoOn f ys := fun x hx y hy hxy => hf x (h x hx) y (h y hy) hxy

/-- Lexicographic comparison is preserved by maps that are monotone on the entries. -/
theorem map_lt_map {f : A → B} : ∀ {p q : List A}, (∀ x ∈ p, ∀ y ∈ q, x < y → f x < f y) →
    (∀ x ∈ p, ∀ y ∈ q, f x = f y → x = y) → p < q → p.map f < q.map f
  | [], _ :: _, _, _, _ => List.Lex.nil
  | a :: p, b :: q, hf, hi, h => by
      cases h with
      | rel h => exact List.Lex.rel (hf a List.mem_cons_self b List.mem_cons_self h)
      | cons h =>
          exact List.Lex.cons (map_lt_map
            (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
            (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) h)

theorem sepPieces_map {f : A → B} {μ : A} : ∀ {xs : List A},
    (∀ x ∈ xs, f x = f μ → x = μ) →
    sepPieces (f μ) (xs.map f) = (sepPieces μ xs).map (List.map f)
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.map_cons, sepPieces]
      have ih := sepPieces_map (fun y hy => h y (List.mem_cons_of_mem _ hy))
      by_cases hx : x = μ
      · subst hx
        simp only [ite_true, List.map_cons, List.map_nil]
        rw [ih]
      · have hfx : f x ≠ f μ := fun e => hx (h x List.mem_cons_self e)
        simp only [hfx, hx, ite_false]
        rw [ih]
        cases sepPieces μ xs with
        | nil => rfl
        | cons p ps => rfl

theorem md_map {f : A → B} {xs : List A} (hf : MonoOn f xs) :
    List.md B (xs.map f) = (List.md A xs).map (List.map f) := by
  cases xs with
  | nil => rfl
  | cons a as =>
      obtain ⟨μ, hμ⟩ := min?_isSome (show a :: as ≠ [] by simp)
      have hs := min?_spec hμ
      rw [md_eq hμ]
      have hfm : f μ ∈ (a :: as).map f := List.mem_map_of_mem hs.1
      have hall : AllGe (f μ) ((a :: as).map f) := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hf.le hs.1 hx (hs.2 x hx)
      rw [Mbek.md_of_min hfm hall]
      exact sepPieces_map (fun x hx e => hf.inj hx hs.1 e)

theorem NF_map (n : Nat) : ∀ {A B : Type} [LT A] [strict_linear_order A] [DecidableEq A]
    [DecidableLT A] [LT B] [strict_linear_order B] [DecidableEq B] [DecidableLT B]
    (f : A → B) (xs : List A), NF A n xs → MonoOn f xs → NF B n (xs.map f) := by
  induction n with
  | zero =>
      intro A B _ _ _ _ _ _ _ _ f xs h hf
      show List.Pairwise _ _
      have h' : List.Pairwise (fun x y : A => y < x ∨ y = x) xs := h
      rw [List.pairwise_map]
      have : ∀ x ∈ xs, ∀ y ∈ xs, (y < x ∨ y = x) → (f y < f x ∨ f y = f x) :=
        fun x hx y hy hyx => hf.le hy hx hyx
      exact List.Pairwise.imp_of_mem (fun hx hy hxy => this _ hx _ hy hxy) h'
  | succ n ih =>
      intro A B _ _ _ _ _ _ _ _ f xs h hf
      induction h with
      | mk xs h₁ h₂ ih₂ =>
          rw [NF_succ_iff, md_map hf]
          have hsub : ∀ p ∈ List.md A xs, ∀ x ∈ p, x ∈ xs := by
            intro p hp x hx
            cases xs with
            | nil => cases hp
            | cons a as =>
                obtain ⟨μ, hμ⟩ := min?_isSome (show a :: as ≠ [] by simp)
                rw [md_eq hμ] at hp
                exact (mem_of_mem_sepPieces μ _ p hp x hx).1
          refine ⟨?_, ?_⟩
          · apply ih (List.map f) (List.md A xs) h₁
            intro p hp q hq hpq
            exact map_lt_map
              (fun x hx y hy hxy => hf x (hsub p hp x hx) y (hsub q hq y hy) hxy)
              (fun x hx y hy e => hf.inj (hsub p hp x hx) (hsub q hq y hy) e) hpq
          · intro ys hys
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hys
            exact ih₂ p hp (hf.sub (hsub p hp))

end

end GenBek
