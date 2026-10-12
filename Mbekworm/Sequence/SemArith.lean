import Mbekworm.Sequence.Transfer
import Mbekworm.Sequence.SemDefs

/-!
# Arithmetic of rank-one terms

Order and addition of summand chains, ordinal addition `oadd`, `-1 + x`,
left subtraction, normal forms of sums, `ω^y` and its inverse `logA`, and the
unfolding equations of the worm valuation.
-/

open T

namespace Mbek

/-!
## Auxiliary facts about rank-one terms used by the translations
-/

theorem T.add_assoc' (a b c : T) : T.add (T.add a b) c = T.add a (T.add b c) :=
  Rank1Termination.add_assoc a b c

theorem T.le_add_right (C x : T) : C < T.add C x ∨ C = T.add C x := by
  cases x with
  | Z => rw [T.add_Z]; exact Or.inr rfl
  | P i u v => exact Or.inl (add_lt_add_of_ne_Z _ _ (by intro h; cases h))

/-- `n` copies of the summand `P i x Z`. -/
def T.copies (i : Nat) (x : T) : Nat → T
  | 0 => Z
  | n + 1 => P i x (T.copies i x n)

theorem T.mul_ofNat_eq_copies (i : Nat) (x : T) (n : Nat) :
    T.mul (P i x Z) (T.ofNat n) = T.copies i x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mul_succ_shape, ih]; rfl

end Mbek

namespace Sem

/-!
## Basic facts about summand chains used by the semantics
-/

/-! ### Order basics on `T` -/

theorem lt_irr (a : T) : ¬ a < a := lt_irrefl_thm a

theorem lt_tr {a b c : T} (h₁ : a < b) (h₂ : b < c) : a < c := lt_trans_thm a b c h₁ h₂

theorem le_refl' (a : T) : a ≤ a := Or.inr rfl

theorem le_of_lt' {a b : T} (h : a < b) : a ≤ b := Or.inl h

theorem lt_of_le_of_lt' {a b c : T} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  rcases h₁ with h₁ | rfl
  · exact lt_tr h₁ h₂
  · exact h₂

theorem lt_of_lt_of_le' {a b c : T} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rcases h₂ with h₂ | rfl
  · exact lt_tr h₁ h₂
  · exact h₁

theorem le_tr {a b c : T} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rcases h₁ with h₁ | rfl
  · exact Or.inl (lt_of_lt_of_le' h₁ h₂)
  · exact h₂

theorem not_lt_of_le' {a b : T} (h : a ≤ b) : ¬ b < a := by
  intro h'
  rcases h with h | rfl
  · exact lt_irr _ (lt_tr h h')
  · exact lt_irr _ h'

theorem le_of_not_lt' {a b : T} (h : ¬ b < a) : a ≤ b := by
  rcases lt_total_thm a b with h' | h' | h'
  · exact Or.inl h'
  · exact absurd h' h
  · exact Or.inr h'

theorem le_antisymm' {a b : T} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  rcases h₁ with h₁ | h₁
  · exact absurd h₁ (not_lt_of_le' h₂)
  · exact h₁

theorem ne_of_lt'' {a b : T} (h : a < b) : a ≠ b := fun e => lt_irr _ (e ▸ h)

theorem Z_lt_P' (i : Nat) (a b : T) : Z < P i a b := T.Lt.Z_lt_P i a b

theorem not_lt_Z' (a : T) : ¬ a < Z := fun h => lt_Z_inv h

theorem lt_single {i j : Nat} {a b c : T} (h : P i a b < P j c Z) : i < j ∨ (i = j ∧ a < c) := by
  rcases lt_inv _ _ _ _ _ _ h with h | ⟨e, h⟩ | ⟨_, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, h⟩
  · exact absurd h (fun h => lt_Z_inv h)

theorem lt_P0 {i : Nat} {a b c : T} (h : P i a b < P 0 c Z) : i = 0 ∧ a < c :=
  (lt_single h).resolve_left (Nat.not_lt_zero _)

theorem lt_tail {i : Nat} {a b d : T} (h : P i a b < P i a d) : b < d := by
  rcases lt_inv _ _ _ _ _ _ h with h | ⟨_, h⟩ | ⟨_, _, h⟩
  · exact absurd h (Nat.lt_irrefl _)
  · exact absurd h (lt_irrefl_thm _)
  · exact h

theorem Z_le' (a : T) : Z ≤ a := T.Z_le a

/-- A summand comparison decides the comparison of chains starting with it. -/
theorem P_lt_P_of_head_lt {i j : Nat} {a c : T} (b d : T) (h : P i a Z < P j c Z) :
    P i a b < P j c d := by
  rcases lt_inv i a Z j c Z h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
  · exact T.Lt.p_head _ _ _ _ _ _ h'
  · exact T.Lt.p_mid _ _ _ _ _ h'
  · exact absurd h' (not_lt_Z' _)

theorem head_le_of_P_lt {i j : Nat} {a c b d : T} (h : P i a b < P j c d) :
    P i a Z ≤ P j c Z := by
  rcases lt_inv i a b j c d h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, _⟩
  · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h')
  · exact Or.inl (T.Lt.p_mid _ _ _ _ _ h')
  · exact Or.inr rfl

theorem lt_of_head_lt {x y : T} (h : T.head x < T.head y) : x < y := by
  cases y with
  | Z => exact absurd h (not_lt_Z' _)
  | P j c d =>
      cases x with
      | Z => exact Z_lt_P' _ _ _
      | P i a b => exact P_lt_P_of_head_lt b d h

theorem head_le_of_lt {x y : T} (h : x < y) : T.head x ≤ T.head y := T.head_mono h

theorem P_le_P_tail {i : Nat} {a b d : T} (h : b ≤ d) : P i a b ≤ P i a d := by
  rcases h with h | rfl
  · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
  · exact le_refl' _

/-! ### Appending chains -/

theorem add_Z_left' (a : T) : T.add Z a = a := rfl

theorem add_P (i : Nat) (a b y : T) : T.add (P i a b) y = P i a (T.add b y) := T.P_add_eq i a b y

theorem add_assoc'' (a b c : T) : T.add (T.add a b) c = T.add a (T.add b c) :=
  Mbek.T.add_assoc' a b c

theorem add_eq_Z_iff {a b : T} : T.add a b = Z ↔ a = Z ∧ b = Z := by
  cases a with
  | Z => simp [T.add]
  | P i c d =>
      rw [add_P]
      constructor
      · intro h; cases h
      · rintro ⟨h, _⟩; cases h

theorem add_lt_add_left_iff (C : T) {x y : T} : T.add C x < T.add C y ↔ x < y := by
  induction C with
  | Z => exact Iff.rfl
  | P i a b _ ih =>
      rw [add_P, add_P]
      constructor
      · intro h
        rcases lt_inv _ _ _ _ _ _ h with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (Nat.lt_irrefl _)
        · exact absurd h (lt_irr _)
        · exact ih.mp h
      · intro h; exact T.Lt.p_tail _ _ _ _ (ih.mpr h)

theorem add_le_add_left_iff (C : T) {x y : T} : T.add C x ≤ T.add C y ↔ x ≤ y := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((add_lt_add_left_iff C).mp h)
    · right
      induction C with
      | Z => exact h
      | P i a b _ ih => rw [add_P, add_P] at h; injection h with _ _ h; exact ih h
  · rintro (h | rfl)
    · exact Or.inl ((add_lt_add_left_iff C).mpr h)
    · exact le_refl' _

theorem le_add_right' (C x : T) : C ≤ T.add C x := Mbek.T.le_add_right C x

theorem lt_add_of_ne (C : T) {x : T} (h : x ≠ Z) : C < T.add C x := add_lt_add_of_ne_Z C x h

/-- If `x < C` and `x` is not a prefix-extension, then `x` stays below any extension of `C`. -/
theorem lt_add_of_lt (C D : T) {x : T} (h : x < C) : x < T.add C D := lt_of_lt_of_le' h (le_add_right' C D)

theorem head_add_of_ne {C : T} (h : C ≠ Z) (D : T) : T.head (T.add C D) = T.head C := by
  cases C with
  | Z => exact absurd rfl h
  | P i a b => rw [add_P]; rfl

/-! ### Descending chains -/

/-- The summands of a chain are non-increasing. -/
def Desc : T → Prop
  | Z => True
  | P i a b => T.head b ≤ P i a Z ∧ Desc b

theorem Desc.tail {i : Nat} {a b : T} (h : Desc (P i a b)) : Desc b := h.2

theorem Desc.hd {i : Nat} {a b : T} (h : Desc (P i a b)) : T.head b ≤ P i a Z := h.1

theorem Desc.single (i : Nat) (a : T) : Desc (P i a Z) := ⟨T.Z_le _, trivial⟩

theorem isNF1_desc : ∀ {x : T}, T.isNF1 x → Desc x
  | Z, _ => trivial
  | P _ _ _, h => by
      have h' := T.isNF1_P_inv _ _ _ h
      exact ⟨h'.2.2.2, isNF1_desc h'.2.1⟩

/-- The last summand of a chain. -/
def lastS : T → T
  | Z => Z
  | P i a Z => P i a Z
  | P _ _ (P j c d) => lastS (P j c d)

theorem Desc.add : ∀ {C D : T}, Desc C → Desc D →
    (∀ i a b, C = P i a b → T.head D ≤ T.head (lastS C)) → Desc (T.add C D)
  | Z, D, _, hD, _ => hD
  | P i a b, D, hC, hD, hlast => by
      rw [add_P]
      refine ⟨?_, ?_⟩
      · cases b with
        | Z =>
            have := hlast i a Z rfl
            simpa [T.add, lastS, T.head] using this
        | P j c d => rw [head_add_of_ne (by intro h; cases h)]; exact hC.hd
      · cases b with
        | Z => exact hD
        | P j c d =>
            refine Desc.add hC.tail hD ?_
            intro i' a' b' he
            have := hlast i a (P j c d) rfl
            rw [he] at this ⊢
            simpa [lastS] using this

/-! ### Countable chains -/

/-- Countable chains: all summands have index `0`. -/
def Cnt : T → Prop
  | Z => True
  | P i _ b => i = 0 ∧ Cnt b

theorem Cnt.tail {i : Nat} {a b : T} (h : Cnt (P i a b)) : Cnt b := h.2

theorem Cnt.idx {i : Nat} {a b : T} (h : Cnt (P i a b)) : i = 0 := h.1

theorem Cnt_lt_Om : ∀ {x : T}, Cnt x → x < Om
  | Z, _ => Z_lt_P' _ _ _
  | P i a b, h => by
      rw [h.idx]
      exact T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one

theorem Cnt_of_lt_Om : ∀ {x : T}, Desc x → x < Om → Cnt x
  | Z, _, _ => trivial
  | P i a b, hd, h => by
      have hi : i = 0 := by
        rcases lt_inv i a b 1 Z Z h with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · omega
        · exact absurd h (not_lt_Z' _)
        · exact absurd h (not_lt_Z' _)
      subst hi
      refine ⟨rfl, Cnt_of_lt_Om hd.tail ?_⟩
      exact lt_of_head_lt (lt_of_le_of_lt' hd.hd (T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one))

theorem Cnt.add : ∀ {C D : T}, Cnt C → Cnt D → Cnt (T.add C D)
  | Z, _, _, hD => hD
  | P _ _ _, _, hC, hD => by rw [add_P]; exact ⟨hC.idx, Cnt.add hC.tail hD⟩

/-!
## Ordinal addition, `-1 + x`, `1 + x` and left subtraction on chains
-/

/-! ### `lastS` -/

theorem lastS_P_P (i : Nat) (a : T) (j : Nat) (c d : T) :
    lastS (P i a (P j c d)) = lastS (P j c d) := rfl

theorem Desc.lastS_le_head : ∀ {x : T}, Desc x → lastS x ≤ T.head x
  | Z, _ => le_refl' _
  | P i a Z, _ => le_refl' _
  | P i a (P j c d), h => by
      rw [lastS_P_P]
      exact le_tr (Desc.lastS_le_head h.tail) h.hd

theorem lastS_add_of_ne : ∀ (C : T) {D : T}, D ≠ Z → lastS (T.add C D) = lastS D
  | Z, _, _ => rfl
  | P i a b, D, hD => by
      rw [add_P]
      cases hb : T.add b D with
      | Z => exact absurd (add_eq_Z_iff.mp hb).2 hD
      | P j c d => rw [lastS_P_P, ← hb]; exact lastS_add_of_ne b hD

/-! ### Ordinal addition -/

theorem oadd_Z_left (y : T) : oadd Z y = y := rfl

theorem oadd_P (i : Nat) (a b y : T) :
    oadd (P i a b) y = if P i a Z < T.head y then y else P i a (oadd b y) := rfl

theorem oadd_P_of_not_lt {i : Nat} {a b y : T} (h : ¬ P i a Z < T.head y) :
    oadd (P i a b) y = P i a (oadd b y) := by
  rw [oadd_P, if_neg h]

theorem oadd_Z_right : ∀ x : T, oadd x Z = x
  | Z => rfl
  | P i a b => by
      rw [oadd_P_of_not_lt (not_lt_Z' _), oadd_Z_right b]

theorem oadd_P_of_lt {i : Nat} {a b y : T} (h : P i a Z < T.head y) :
    oadd (P i a b) y = y := by
  rw [oadd_P, if_pos h]

/-- No absorption happens when the head of `y` is at most the last summand of `x`. -/
theorem oadd_eq_add : ∀ {x y : T}, Desc x → T.head y ≤ lastS x → oadd x y = T.add x y
  | Z, y, _, _ => rfl
  | P i a b, y, hx, hy => by
      have hle : T.head y ≤ P i a Z := le_tr hy (Desc.lastS_le_head hx)
      rw [oadd_P_of_not_lt (not_lt_of_le' hle), add_P]
      congr 1
      cases b with
      | Z => rfl
      | P j c d => exact oadd_eq_add hx.tail (by rw [lastS_P_P] at hy; exact hy)

/-- Adding `1` never absorbs. -/
theorem oadd_one : ∀ x : T, oadd x one = T.add x one
  | Z => rfl
  | P i a b => by
      have : ¬ P i a Z < T.head one := by
        intro h
        rcases lt_inv _ _ _ _ _ _ h with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · omega
        · exact not_lt_Z' _ h
        · exact not_lt_Z' _ h
      rw [oadd_P_of_not_lt this, add_P, oadd_one b]

theorem oadd_desc : ∀ {x y : T}, Desc x → Desc y → Desc (oadd x y)
  | Z, _, _, hy => hy
  | P i a b, y, hx, hy => by
      rw [oadd_P]
      split
      · exact hy
      · rename_i hlt
        refine ⟨?_, oadd_desc hx.tail hy⟩
        cases b with
        | Z => rw [oadd_Z_left]; exact le_of_not_lt' hlt
        | P j c d =>
            rw [oadd_P]
            split
            · exact le_of_not_lt' hlt
            · exact hx.hd

theorem oadd_cnt : ∀ {x y : T}, Cnt x → Cnt y → Cnt (oadd x y)
  | Z, _, _, hy => hy
  | P i a b, y, hx, hy => by
      rw [oadd_P]
      split
      · exact hy
      · exact ⟨hx.idx, oadd_cnt hx.tail hy⟩

/-- The head of a sum. -/
theorem head_oadd_le : ∀ (x y : T), T.head x ≤ T.head (oadd x y)
  | Z, y => Z_le' _
  | P i a b, y => by
      rw [oadd_P]
      split
      · rename_i h; exact Or.inl h
      · exact le_refl' _

/-- A descending chain is above its tail. -/
theorem tail_lt_of_desc : ∀ {i : Nat} {a d : T}, Desc (P i a d) → d < P i a d
  | _, _, Z, _ => Z_lt_P' _ _ _
  | i, a, P j c e, h => by
      rcases h.hd with h' | h'
      · exact P_lt_P_of_head_lt _ _ h'
      · simp only [T.head] at h'
        injection h' with h1 h2
        subst h1 h2
        exact T.Lt.p_tail _ _ _ _ (tail_lt_of_desc h.tail)

theorem le_oadd_right : ∀ (x y : T), Desc y → y ≤ oadd x y
  | Z, y, _ => le_refl' _
  | P i a b, y, hy => by
      rw [oadd_P]
      split
      · exact le_refl' _
      · rename_i h
        cases y with
        | Z => exact Or.inl (Z_lt_P' _ _ _)
        | P j c d =>
            rcases le_of_not_lt' h with h | h
            · exact Or.inl (P_lt_P_of_head_lt _ _ h)
            · simp only [T.head] at h
              injection h with h1 h2
              subst h1 h2
              have := le_oadd_right b (P j c d) hy
              exact P_le_P_tail (le_tr (le_of_lt' (tail_lt_of_desc hy)) this)

/-- Strict monotonicity in the right argument. -/
theorem oadd_lt_oadd_right : ∀ {x y y' : T}, Desc x → y < y' → oadd x y < oadd x y'
  | Z, _, _, _, h => h
  | P i a b, y, y', hx, h => by
      have hhd := head_le_of_lt h
      by_cases h1 : P i a Z < T.head y
      · rw [oadd_P_of_lt h1, oadd_P_of_lt (lt_of_lt_of_le' h1 hhd)]; exact h
      · rw [oadd_P_of_not_lt h1]
        by_cases h2 : P i a Z < T.head y'
        · rw [oadd_P_of_lt h2]
          exact lt_of_head_lt (by simpa [T.head] using h2)
        · rw [oadd_P_of_not_lt h2]
          exact T.Lt.p_tail _ _ _ _ (oadd_lt_oadd_right hx.tail h)

/-!
## Unfolding the worm valuation
-/

/-- Countable normal forms. -/
def Good (x : T) : Prop := T.isNF1 x ∧ Cnt x

/-- One step of the hyperation. -/
def Eom : Nat → T → T → T
  | 0, _, y => y
  | 1, α, y => if α = Z then minus1 (omegaPow y) else if y = Z then Z else phi 0 α (minus1 y)
  | m + 2, α, y => if α = Z then minus1 (E (m + 1) y one) else if y = Z then Z
      else phi (m + 1) (minus1 α) (minus1 y)

theorem foldE_P (f : T → T → T) (i : Nat) (c b x : T) :
    foldE f (P i c b) x = f (logA c) (foldE f b x) := rfl

theorem E_eq (n : Nat) (μ x : T) : E n μ x = foldE (Eom n) μ x := by
  match n with
  | 0 =>
      show x = foldE (Eom 0) μ x
      induction μ with
      | Z => rfl
      | P i c b _ ih => rw [foldE_P, ← ih]; rfl
  | 1 => rfl
  | m + 2 => rfl

theorem E_Z (n : Nat) (x : T) : E n Z x = x := by rw [E_eq]; rfl

theorem E_P (n : Nat) (i : Nat) (c b x : T) : E n (P i c b) x = Eom n (logA c) (E n b x) := by
  rw [E_eq, E_eq, foldE_P]

/-- The `0`-split part of the valuation. -/
def zs (n : Nat) (w : List T) : T :=
  if Z ∈ w then minus1 (o n ((GenBek.sepPieces Z w).map (fun p => o (n + 1) (p.map minus1))))
  else Z

theorem o_nil (n : Nat) : o n [] = Z := by rw [o]

theorem o_zero (w : List T) : o 0 w = cantorT w := by
  cases w with
  | nil => rw [o_nil]; rfl
  | cons b bs => rw [o]

theorem o_succ (n : Nat) (w : List T) (hw : w ≠ []) :
    o (n + 1) w = E (n + 1) (tmin w) (zs n (w.map (leftSub (tmin w)))) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x xs =>
      rw [o]
      simp only [zs]
      split
      · congr 3
        exact List.attach_map_val (f := fun p => o (n + 1) (List.map minus1 p))
      · rfl

/-!
## A toolkit for rank-one normal forms of summand chains
-/

theorem G1_Z (u : Nat) : T.G1 u Z = [] := rfl

theorem G1_P (u i : Nat) (a b : T) :
    T.G1 u (P i a b) = if u ≤ i then [a] ++ T.G1 u a ++ T.G1 u b else T.G1 u b := rfl

theorem G1_P0 (i : Nat) (a b : T) : T.G1 0 (P i a b) = [a] ++ T.G1 0 a ++ T.G1 0 b := by
  rw [G1_P, if_pos (Nat.zero_le i)]

theorem G1_add (u : Nat) : ∀ (x y : T), T.G1 u (T.add x y) = T.G1 u x ++ T.G1 u y
  | Z, y => rfl
  | P i a b, y => by
      rw [add_P, G1_P, G1_P, G1_add u b y]
      split <;> simp

theorem isNF1_P_iff (i : Nat) (a b : T) :
    T.isNF1 (P i a b) ↔ T.isNF1 (P i a Z) ∧ T.isNF1 b ∧ T.head b ≤ P i a Z := by
  constructor
  · intro h
    have h' := T.isNF1_P_inv _ _ _ h
    exact ⟨T.isNF1.p i a Z h'.1 T.isNF1.z h'.2.2.1 (T.Z_le _), h'.2.1, h'.2.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := T.isNF1_P_inv _ _ _ h1
    exact T.isNF1.p i a b h1'.1 h2 h1'.2.2.1 h3

theorem isNF1_P_Z_iff (i : Nat) (a : T) :
    T.isNF1 (P i a Z) ↔ T.isNF1 a ∧ ∀ x ∈ T.G1 i a, x < a := by
  constructor
  · intro h
    have h' := T.isNF1_P_inv _ _ _ h
    exact ⟨h'.1, h'.2.2.1⟩
  · rintro ⟨h1, h2⟩
    exact T.isNF1.p i a Z h1 T.isNF1.z h2 (T.Z_le _)

theorem isNF1_tail {i : Nat} {a b : T} (h : T.isNF1 (P i a b)) : T.isNF1 b :=
  ((isNF1_P_iff i a b).mp h).2.1

theorem isNF1_head {i : Nat} {a b : T} (h : T.isNF1 (P i a b)) : T.isNF1 (P i a Z) :=
  ((isNF1_P_iff i a b).mp h).1

theorem isNF1_arg {i : Nat} {a b : T} (h : T.isNF1 (P i a b)) : T.isNF1 a :=
  (T.isNF1_P_inv _ _ _ h).1

theorem isNF1_G {i : Nat} {a b : T} (h : T.isNF1 (P i a b)) : ∀ x ∈ T.G1 i a, x < a :=
  (T.isNF1_P_inv _ _ _ h).2.2.1

theorem isNF1_hd {i : Nat} {a b : T} (h : T.isNF1 (P i a b)) : T.head b ≤ P i a Z :=
  (T.isNF1_P_inv _ _ _ h).2.2.2

/-- Appending normal forms whose junction is descending. -/
theorem isNF1_add : ∀ {x y : T}, T.isNF1 x → T.isNF1 y → T.head y ≤ lastS x → T.isNF1 (T.add x y)
  | Z, _, _, hy, _ => hy
  | P i a b, y, hx, hy, hl => by
      rw [add_P]
      refine (isNF1_P_iff i a _).mpr ⟨isNF1_head hx, ?_, ?_⟩
      · cases b with
        | Z => exact hy
        | P j c d => exact isNF1_add (isNF1_tail hx) hy (by rw [lastS_P_P] at hl; exact hl)
      · cases b with
        | Z => exact le_tr hl (le_refl' _)
        | P j c d => rw [head_add_of_ne (by intro e; cases e)]; exact isNF1_hd hx

/-- Suffixes of normal forms are normal forms. -/
theorem isNF1_of_add_right : ∀ {pre y : T}, T.isNF1 (T.add pre y) → T.isNF1 y
  | Z, _, h => h
  | P i a b, y, h => by rw [add_P] at h; exact isNF1_of_add_right (isNF1_tail h)

theorem isNF1_of_add_left : ∀ {pre y : T}, T.isNF1 (T.add pre y) → T.isNF1 pre
  | Z, _, _ => T.isNF1.z
  | P i a b, y, h => by
      rw [add_P] at h
      refine (isNF1_P_iff i a b).mpr ⟨isNF1_head h, isNF1_of_add_left (isNF1_tail h), ?_⟩
      have := isNF1_hd h
      cases b with
      | Z => exact T.Z_le _
      | P j c d => rw [head_add_of_ne (by intro e; cases e)] at this; exact this

/-- Sums with absorption of normal forms are normal forms. -/
theorem isNF1_oadd : ∀ {x y : T}, T.isNF1 x → T.isNF1 y → T.isNF1 (oadd x y)
  | Z, _, _, hy => hy
  | P i a b, y, hx, hy => by
      rw [oadd_P]
      split
      · exact hy
      · rename_i hlt
        refine (isNF1_P_iff i a _).mpr ⟨isNF1_head hx, isNF1_oadd (isNF1_tail hx) hy, ?_⟩
        cases b with
        | Z => rw [oadd_Z_left]; exact le_of_not_lt' hlt
        | P j c d =>
            rw [oadd_P]
            split
            · exact le_of_not_lt' hlt
            · simpa [T.head] using isNF1_hd hx

/-- Components of a countable normal form are bounded by its head argument. -/
theorem comps_le_head_arg : ∀ {c b : T}, T.isNF1 (P 0 c b) → ∀ x ∈ T.G1 0 (P 0 c b), x ≤ c := by
  intro c b
  induction b generalizing c with
  | Z =>
      intro h x hx
      rw [G1_P0, G1_Z, List.append_nil, List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact le_refl' _
      · exact Or.inl (isNF1_G h x hx)
  | P j d e _ ihe =>
      intro h x hx
      rw [G1_P0, List.mem_append, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact le_refl' _
      · exact Or.inl (isNF1_G h x hx)
      · have hd := isNF1_hd h
        have hj : j = 0 := by
          rcases hd with hd | hd
          · rcases lt_inv _ _ _ _ _ _ hd with h' | ⟨_, _⟩ | ⟨_, _, h'⟩
            · omega
            · assumption
            · exact absurd h' (not_lt_Z' _)
          · simp only [T.head] at hd; injection hd
        subst hj
        have hdc : d ≤ c := by
          rcases hd with hd | hd
          · rcases lt_inv _ _ _ _ _ _ hd with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
            · omega
            · exact Or.inl h'
            · exact absurd h' (not_lt_Z' _)
          · simp only [T.head] at hd; injection hd with _ h'; exact Or.inr h'
        exact le_tr (ihe (isNF1_tail h) x hx) hdc

/-- `G1` is transitive. -/
theorem G1_trans (u : Nat) : ∀ {c x : T}, x ∈ T.G1 u c → ∀ y ∈ T.G1 u x, y ∈ T.G1 u c
  | Z, _, hx, _, _ => absurd hx List.not_mem_nil
  | P i a b, x, hx, y, hy => by
      rw [G1_P] at hx ⊢
      split
      · rename_i hu
        rw [if_pos hu] at hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with (rfl | hx) | hx
        · exact Or.inl (Or.inr hy)
        · exact Or.inl (Or.inr (G1_trans u hx y hy))
        · exact Or.inr (G1_trans u hx y hy)
      · rename_i hu
        rw [if_neg hu] at hx
        exact G1_trans u hx y hy

/-- Countable components of a normal form are below the principal term over it. -/
theorem lt_psi_of_comp {c : T} (hc : T.isNF1 (P 0 c Z)) :
    ∀ x ∈ T.G1 0 c, Cnt x → x < P 0 c Z := by
  intro x hx hcx
  cases x with
  | Z => exact Z_lt_P' _ _ _
  | P i a b =>
      have hi : i = 0 := hcx.idx
      subst hi
      apply P_lt_P_of_head_lt
      apply T.Lt.p_mid
      have hsub : a ∈ T.G1 0 c := G1_trans 0 hx a (by rw [G1_P0]; simp)
      exact isNF1_G hc a hsub

/-!
## `-1 + x`, left subtraction, `log` and `ω^x` on countable normal forms
-/

/-! ### Goodness basics -/

theorem good_Z : Good Z := ⟨T.isNF1.z, trivial⟩

theorem good_one : Good one :=
  ⟨T.isNF1.p 0 Z Z T.isNF1.z T.isNF1.z (by simp [T.G1]) (T.Z_le _), rfl, trivial⟩

theorem Good.nf {x : T} (h : Good x) : T.isNF1 x := h.1

theorem Good.cnt {x : T} (h : Good x) : Cnt x := h.2

theorem Good.desc {x : T} (h : Good x) : Desc x := isNF1_desc h.1

theorem Good.tail {i : Nat} {a b : T} (h : Good (P i a b)) : Good b :=
  ⟨isNF1_tail h.1, h.2.tail⟩

theorem Good.idx {i : Nat} {a b : T} (h : Good (P i a b)) : i = 0 := h.2.idx

theorem good_ofNat : ∀ n, Good (T.ofNat n)
  | 0 => good_Z
  | n + 1 => ⟨IsN_isNF1 _ (ofNat_IsN (n + 1)), rfl, (good_ofNat n).cnt⟩

theorem good_oadd {x y : T} (hx : Good x) (hy : Good y) : Good (oadd x y) :=
  ⟨isNF1_oadd hx.nf hy.nf, oadd_cnt hx.cnt hy.cnt⟩

/-- Heads of a countable chain: `P 0 c Z ≤ P 0 d Z ↔ c ≤ d`. -/
theorem P0_le_P0_iff {c d : T} : P 0 c Z ≤ P 0 d Z ↔ c ≤ d := by
  constructor
  · rintro (h | h)
    · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
      · exact absurd h' (Nat.lt_irrefl 0)
      · exact Or.inl h'
      · exact absurd h' (not_lt_Z' _)
    · injection h with _ h; exact Or.inr h
  · rintro (h | rfl)
    · exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
    · exact le_refl' _

theorem P0_lt_P0_iff {c d : T} : P 0 c Z < P 0 d Z ↔ c < d := by
  constructor
  · intro h
    rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
    · exact absurd h' (Nat.lt_irrefl 0)
    · exact h'
    · exact absurd h' (not_lt_Z' _)
  · intro h; exact T.Lt.p_mid _ _ _ _ _ h

/-! ### `-1 + x` -/

theorem minus1_one_add (b : T) : minus1 (P 0 Z b) = b := rfl

theorem minus1_of_ne {a b : T} (ha : a ≠ Z) : minus1 (P 0 a b) = P 0 a b := by
  cases a with
  | Z => exact absurd rfl ha
  | P _ _ _ => rfl

theorem good_minus1 {x : T} (h : Good x) : Good (minus1 x) := by
  cases x with
  | Z => exact h
  | P i a b =>
      have hi := h.idx
      subst hi
      cases a with
      | Z => exact h.tail
      | P _ _ _ => exact h

theorem minus1_lt_minus1 {x y : T} (hx : Good x) (hy : Good y) (hx0 : x ≠ Z) (h : x < y) :
    minus1 x < minus1 y := by
  cases x with
  | Z => exact absurd rfl hx0
  | P i a b =>
      cases y with
      | Z => exact absurd h (not_lt_Z' _)
      | P j c d =>
          have hi := hx.idx
          have hj := hy.idx
          subst hi hj
          by_cases ha : a = Z
          · subst ha
            rw [minus1_one_add]
            by_cases hc : c = Z
            · subst hc
              rw [minus1_one_add]
              rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
              · exact absurd h' (Nat.lt_irrefl 0)
              · exact absurd h' (not_lt_Z' _)
              · exact h'
            · rw [minus1_of_ne hc]
              exact lt_tr (tail_lt_of_desc hx.desc) h
          · rw [minus1_of_ne ha]
            have hac : P 0 a Z ≤ P 0 c Z := head_le_of_P_lt h
            have hc : c ≠ Z := by
              intro e; subst e
              rcases P0_le_P0_iff.mp hac with h' | h'
              · exact not_lt_Z' _ h'
              · exact ha h'
            rw [minus1_of_ne hc]
            exact h

theorem oadd_one_minus1 {x : T} (hx : Good x) (h : x ≠ Z) : oadd one (minus1 x) = x := by
  cases x with
  | Z => exact absurd rfl h
  | P i a b =>
      have hi := hx.idx
      subst hi
      by_cases ha : a = Z
      · subst ha
        rw [minus1_one_add]
        show oadd (P 0 Z Z) b = P 0 Z b
        rw [oadd_P_of_not_lt (not_lt_of_le' hx.desc.hd), oadd_Z_left]
      · rw [minus1_of_ne ha]
        show oadd (P 0 Z Z) (P 0 a b) = P 0 a b
        apply oadd_P_of_lt
        show P 0 Z Z < P 0 a Z
        apply T.Lt.p_mid
        cases a with
        | Z => exact absurd rfl ha
        | P _ _ _ => exact Z_lt_P' _ _ _

/-! ### Suffixes -/

/-- `y` is a suffix of `x`. -/
def IsSuf (y x : T) : Prop := ∃ pre, x = T.add pre y

theorem IsSuf.refl (x : T) : IsSuf x x := ⟨Z, rfl⟩

theorem IsSuf.tail {y : T} {i : Nat} {a b : T} (h : IsSuf y b) : IsSuf y (P i a b) := by
  obtain ⟨pre, rfl⟩ := h
  exact ⟨P i a pre, by rw [add_P]⟩

theorem IsSuf.le {y x : T} (hx : Desc x) (h : IsSuf y x) : y ≤ x := by
  obtain ⟨pre, rfl⟩ := h
  induction pre with
  | Z => exact le_refl' _
  | P i a b _ ih =>
      rw [add_P] at hx ⊢
      exact le_tr (ih hx.tail) (le_of_lt' (tail_lt_of_desc hx))

theorem IsSuf.good {y x : T} (hx : Good x) (h : IsSuf y x) : Good y := by
  obtain ⟨pre, rfl⟩ := h
  refine ⟨isNF1_of_add_right hx.nf, ?_⟩
  have := hx.cnt
  clear hx
  induction pre with
  | Z => exact this
  | P i a b _ ih => rw [add_P] at this; exact ih this.tail

theorem IsSuf.head_le {y x : T} (hx : Desc x) (h : IsSuf y x) : T.head y ≤ T.head x := by
  rcases h.le hx with h' | h'
  · exact head_le_of_lt h'
  · rw [h']; exact le_refl' _

/-! ### Left subtraction -/

theorem leftSub_Z_left (x : T) : leftSub Z x = x := by cases x <;> rfl

theorem leftSub_P_Z (i : Nat) (a b : T) : leftSub (P i a b) Z = Z := rfl

theorem leftSub_P_P (i : Nat) (a b : T) (j : Nat) (c d : T) :
    leftSub (P i a b) (P j c d) = if i = j ∧ a = c then leftSub b d else P j c d := rfl

theorem leftSub_self : ∀ x : T, leftSub x x = Z
  | Z => rfl
  | P i a b => by
      rw [leftSub_P_P, if_pos ⟨rfl, rfl⟩, leftSub_self b]

theorem leftSub_suf : ∀ (ν x : T), IsSuf (leftSub ν x) x
  | Z, x => by rw [leftSub_Z_left]; exact IsSuf.refl x
  | P i a b, Z => by rw [leftSub_P_Z]; exact IsSuf.refl Z
  | P i a b, P j c d => by
      rw [leftSub_P_P]
      split
      · exact (leftSub_suf b d).tail
      · exact IsSuf.refl _

theorem good_leftSub {ν x : T} (_hν : Good ν) (hx : Good x) : Good (leftSub ν x) :=
  (leftSub_suf ν x).good hx

/-- If `z` starts strictly below `x`, subtracting it does nothing. -/
theorem leftSub_of_head_lt {z x : T} (h : z = Z ∨ T.head z < T.head x) : leftSub z x = x := by
  rcases h with rfl | h
  · exact leftSub_Z_left x
  · cases z with
    | Z => exact leftSub_Z_left x
    | P i a b =>
        cases x with
        | Z => exact absurd h (not_lt_Z' _)
        | P j c d =>
            rw [leftSub_P_P, if_neg]
            rintro ⟨rfl, rfl⟩
            exact lt_irr _ h

theorem head_lt_of_le_of_ne {ν x : T} {i : Nat} {a b : T} {j : Nat} {c d : T}
    (hν : ν = P i a b) (hx : x = P j c d) (h : ν ≤ x) (hne : ¬ (i = j ∧ a = c)) :
    P i a Z < P j c Z := by
  subst hν hx
  rcases h with h | h
  · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, _⟩
    · exact T.Lt.p_head _ _ _ _ _ _ h'
    · exact T.Lt.p_mid _ _ _ _ _ h'
    · exact absurd ⟨rfl, rfl⟩ hne
  · injection h with h1 h2 _
    exact absurd ⟨h1, h2⟩ hne

theorem oadd_leftSub : ∀ {ν x : T}, Good ν → Good x → ν ≤ x → oadd ν (leftSub ν x) = x
  | Z, x, _, _, _ => by rw [leftSub_Z_left, oadd_Z_left]
  | P i a b, Z, _, _, h => by
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i a b, P j c d, hν, hx, h => by
      rw [leftSub_P_P]
      split
      · rename_i hh
        obtain ⟨rfl, rfl⟩ := hh
        have hbd : b ≤ d := by
          rcases h with h | h
          · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
            · exact absurd h' (Nat.lt_irrefl _)
            · exact absurd h' (lt_irr _)
            · exact Or.inl h'
          · injection h with _ _ h; exact Or.inr h
        have hsuf := leftSub_suf b d
        have hhd : T.head (leftSub b d) ≤ P i a Z := le_tr (hsuf.head_le hx.desc.tail) hx.desc.hd
        rw [oadd_P_of_not_lt (not_lt_of_le' hhd), oadd_leftSub hν.tail hx.tail hbd]
      · rename_i hh
        exact oadd_P_of_lt (head_lt_of_le_of_ne rfl rfl h hh)

theorem leftSub_lt_leftSub : ∀ {ν x y : T}, Good ν → Good x → Good y → ν ≤ x → x < y →
    leftSub ν x < leftSub ν y
  | Z, x, y, _, _, _, _, h => by rw [leftSub_Z_left, leftSub_Z_left]; exact h
  | P i a b, Z, _, _, _, _, h, _ => by
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i a b, P j c d, Z, _, _, _, _, h => absurd h (not_lt_Z' _)
  | P i a b, P j c d, P k e f, hν, hx, hy, h₁, h₂ => by
      rw [leftSub_P_P, leftSub_P_P]
      by_cases hxx : i = j ∧ a = c
      · obtain ⟨rfl, rfl⟩ := hxx
        rw [if_pos ⟨rfl, rfl⟩]
        have hbd : b ≤ d := by
          rcases h₁ with h | h
          · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
            · exact absurd h' (Nat.lt_irrefl _)
            · exact absurd h' (lt_irr _)
            · exact Or.inl h'
          · injection h with _ _ h; exact Or.inr h
        by_cases hyy : i = k ∧ a = e
        · obtain ⟨rfl, rfl⟩ := hyy
          rw [if_pos ⟨rfl, rfl⟩]
          have hdf : d < f := lt_tail h₂
          exact leftSub_lt_leftSub hν.tail hx.tail hy.tail hbd hdf
        · rw [if_neg hyy]
          exact lt_of_le_of_lt' ((leftSub_suf b d).le hx.desc.tail)
            (lt_tr (tail_lt_of_desc hx.desc) h₂)
      · rw [if_neg hxx]
        have hlt := head_lt_of_le_of_ne rfl rfl h₁ hxx
        have hyy : ¬ (i = k ∧ a = e) := by
          rintro ⟨rfl, rfl⟩
          have := head_le_of_P_lt h₂
          exact not_lt_of_le' this hlt
        rw [if_neg hyy]
        exact h₂

theorem leftSub_le_leftSub {ν x y : T} (hν : Good ν) (hx : Good x) (hy : Good y) (h₁ : ν ≤ x)
    (h₂ : x ≤ y) : leftSub ν x ≤ leftSub ν y := by
  rcases h₂ with h₂ | rfl
  · exact Or.inl (leftSub_lt_leftSub hν hx hy h₁ h₂)
  · exact le_refl' _

theorem leftSub_leftSub : ∀ {ν μ x : T}, Good ν → Good μ → Good x → ν ≤ μ → μ ≤ x →
    leftSub (leftSub ν μ) (leftSub ν x) = leftSub μ x
  | Z, μ, x, _, _, _, _, _ => by rw [leftSub_Z_left, leftSub_Z_left]
  | P i a b, Z, _, _, _, _, h, _ => by
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i a b, P j c d, Z, _, _, _, _, h => by
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i a b, P j c d, P k e f, hν, hμ, hx, h₁, h₂ => by
      by_cases hμμ : i = j ∧ a = c
      · obtain ⟨rfl, rfl⟩ := hμμ
        have hbd : b ≤ d := by
          rcases h₁ with h | h
          · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
            · exact absurd h' (Nat.lt_irrefl _)
            · exact absurd h' (lt_irr _)
            · exact Or.inl h'
          · injection h with _ _ h; exact Or.inr h
        rw [leftSub_P_P i a b i a d, if_pos ⟨rfl, rfl⟩]
        by_cases hxx : i = k ∧ a = e
        · obtain ⟨rfl, rfl⟩ := hxx
          have hdf : d ≤ f := by
            rcases h₂ with h | h
            · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
              · exact absurd h' (Nat.lt_irrefl _)
              · exact absurd h' (lt_irr _)
              · exact Or.inl h'
            · injection h with _ _ h; exact Or.inr h
          rw [leftSub_P_P i a b i a f, if_pos ⟨rfl, rfl⟩, leftSub_P_P i a d i a f, if_pos ⟨rfl, rfl⟩]
          exact leftSub_leftSub hν.tail hμ.tail hx.tail hbd hdf
        · rw [leftSub_P_P i a b k e f, if_neg hxx, leftSub_P_P i a d k e f, if_neg hxx]
          have hlt := head_lt_of_le_of_ne rfl rfl h₂ hxx
          apply leftSub_of_head_lt
          cases hs : leftSub b d with
          | Z => exact Or.inl rfl
          | P _ _ _ =>
              right
              have := (leftSub_suf b d).head_le hμ.desc.tail
              rw [hs] at this
              exact lt_of_le_of_lt' (le_tr this hμ.desc.hd) hlt
      · have hlt := head_lt_of_le_of_ne rfl rfl h₁ hμμ
        have hxx : ¬ (i = k ∧ a = e) := by
          rintro ⟨rfl, rfl⟩
          rcases h₂ with h | h
          · exact not_lt_of_le' (head_le_of_P_lt h) hlt
          · injection h with h1 h2; subst h1 h2; exact lt_irr _ hlt
        rw [leftSub_P_P i a b j c d, if_neg hμμ, leftSub_P_P i a b k e f, if_neg hxx]

theorem leftSub_minus1 {μ x : T} (hμ : Good μ) (hx : Good x) (h0 : μ ≠ Z) (h : μ ≤ x) :
    leftSub (minus1 μ) (minus1 x) = leftSub μ x := by
  cases μ with
  | Z => exact absurd rfl h0
  | P i a b =>
      cases x with
      | Z =>
          rcases h with h | h
          · exact absurd h (not_lt_Z' _)
          · cases h
      | P j c d =>
          have hi := hμ.idx
          have hj := hx.idx
          subst hi hj
          by_cases ha : a = Z
          · subst ha
            rw [minus1_one_add]
            by_cases hc : c = Z
            · subst hc
              rw [minus1_one_add, leftSub_P_P, if_pos ⟨rfl, rfl⟩]
            · rw [minus1_of_ne hc, leftSub_P_P, if_neg (fun hh => hc hh.2.symm)]
              apply leftSub_of_head_lt
              cases b with
              | Z => exact Or.inl rfl
              | P _ _ _ =>
                  right
                  refine lt_of_le_of_lt' hμ.desc.hd ?_
                  apply T.Lt.p_mid
                  cases c with
                  | Z => exact absurd rfl hc
                  | P _ _ _ => exact Z_lt_P' _ _ _
          · rw [minus1_of_ne ha]
            have hc : c ≠ Z := by
              intro e; subst e
              rcases h with h | h
              · rcases P0_le_P0_iff.mp (head_le_of_P_lt h) with h' | h'
                · exact not_lt_Z' _ h'
                · exact ha h'
              · injection h with _ h'; exact ha h'
            rw [minus1_of_ne hc]

/-! ### `log` and `ω^x` -/

theorem uncPart_add_cntPart : ∀ c : T, T.add (uncPart c) (cntPart c) = c
  | Z => rfl
  | P 0 a b => rfl
  | P (i + 1) a b => by
      show T.add (P (i + 1) a (uncPart b)) (cntPart b) = P (i + 1) a b
      rw [add_P, uncPart_add_cntPart b]

/-- The argument of `ω^y`. -/
def omegaArg : T → T
  | Z => Z
  | P i c b =>
    if uncPart c = Z then P i c b
    else if cntPart c = Z then T.add (uncPart c) b
    else T.add (uncPart c) (P i c b)

theorem omegaPow_eq (y : T) : omegaPow y = P 0 (omegaArg y) Z := by
  cases y with
  | Z => rfl
  | P i c b =>
      simp only [omegaPow, omegaArg]
      split
      · rfl
      · split <;> rfl

theorem omegaPow_Z : omegaPow Z = one := rfl

theorem omegaPow_ne_Z (y : T) : omegaPow y ≠ Z := by
  rw [omegaPow_eq]; intro h; cases h

/-- All summands have index `≥ 1`. -/
def Unc : T → Prop
  | Z => True
  | P i _ b => 1 ≤ i ∧ Unc b

theorem unc_uncPart : ∀ c : T, Unc (uncPart c)
  | Z => trivial
  | P 0 _ _ => trivial
  | P (i + 1) a b => ⟨Nat.succ_pos i, unc_uncPart b⟩

theorem cntPart_head : ∀ c : T, cntPart c = Z ∨ ∃ a b, cntPart c = P 0 a b
  | Z => Or.inl rfl
  | P 0 a b => Or.inr ⟨a, b, rfl⟩
  | P (i + 1) a b => cntPart_head b

/-- An uncountable-headed chain dominates countable-headed ones. -/
theorem lt_unc_add {U S : T} (hU : Unc U) (hU0 : U ≠ Z) (S' : T)
    (hS : S = Z ∨ ∃ a b, S = P 0 a b) : S < T.add U S' := by
  cases U with
  | Z => exact absurd rfl hU0
  | P i a b =>
      rw [add_P]
      rcases hS with rfl | ⟨c, d, rfl⟩
      · exact Z_lt_P' _ _ _
      · exact T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hU.1)

/-- Comparison of `U ++ R` decided inside the uncountable parts. -/
theorem unc_add_lt : ∀ {U U' R R' S S' : T}, Unc U → Unc U' →
    (R = Z ∨ ∃ a b, R = P 0 a b) → (R' = Z ∨ ∃ a b, R' = P 0 a b) →
    (S = Z ∨ ∃ a b, S = P 0 a b) → U ≠ U' → T.add U R < T.add U' R' → T.add U S < T.add U' S'
  | Z, Z, _, _, _, _, _, _, _, _, _, hne, _ => absurd rfl hne
  | Z, P j c d, _, _, S, S', _, hU', _, _, hS, _, _ => lt_unc_add hU' (by intro e; cases e) S' hS
  | P i a b, Z, R, R', _, _, hU, _, _, hR', _, _, h => by
      exfalso
      have := lt_unc_add hU (by intro e; cases e) R hR'
      exact lt_irr _ (lt_tr h this)
  | P i a b, P j c d, R, R', S, S', hU, hU', hR, hR', hS, hne, h => by
      rw [add_P, add_P] at h ⊢
      rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
      · exact T.Lt.p_head _ _ _ _ _ _ h'
      · exact T.Lt.p_mid _ _ _ _ _ h'
      · have hbd : b ≠ d := fun e => hne (by rw [e])
        exact T.Lt.p_tail _ _ _ _ (unc_add_lt hU.2 hU'.2 hR hR' hS hbd h')

theorem cnt_head_of_cnt {S : T} (h : Cnt S) : S = Z ∨ ∃ a b, S = P 0 a b := by
  cases S with
  | Z => exact Or.inl rfl
  | P i a b => rw [h.idx]; exact Or.inr ⟨a, b, rfl⟩

theorem omegaArg_ne_Z {y : T} (hy : y ≠ Z) : omegaArg y ≠ Z := by
  cases y with
  | Z => exact absurd rfl hy
  | P i c b =>
      simp only [omegaArg]
      split
      · intro e; cases e
      · rename_i hU
        split
        · intro e; exact hU (add_eq_Z_iff.mp e).1
        · intro e; exact hU (add_eq_Z_iff.mp e).1

theorem uncPart_ne_of_le {c c' : T} (hU : uncPart c ≠ Z) (h : c ≤ c') : uncPart c' ≠ Z := by
  cases c with
  | Z => exact absurd rfl hU
  | P i a b =>
      cases i with
      | zero => exact absurd rfl hU
      | succ i =>
          cases c' with
          | Z =>
              rcases h with h | h
              · exact absurd h (not_lt_Z' _)
              · cases h
          | P j a' b' =>
              cases j with
              | succ j => intro e; cases e
              | zero =>
                  exfalso
                  rcases h with h | h
                  · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨h', _⟩ | ⟨h', _, _⟩
                    · omega
                    · cases h'
                    · cases h'
                  · cases h

theorem omegaArg_lt {y y' : T} (hy : Good y) (hy' : Good y') (h : y < y') :
    omegaArg y < omegaArg y' := by
  cases y with
  | Z =>
      cases y' with
      | Z => exact absurd h (not_lt_Z' _)
      | P _ _ _ =>
          show Z < _
          cases hz : omegaArg (P _ _ _) with
          | Z => exact absurd hz (omegaArg_ne_Z (by intro e; cases e))
          | P _ _ _ => exact Z_lt_P' _ _ _
  | P i c b =>
      cases y' with
      | Z => exact absurd h (not_lt_Z' _)
      | P j c' b' =>
          have hi := hy.idx
          have hj := hy'.idx
          subst hi hj
          have hcc : c ≤ c' := P0_le_P0_iff.mp (head_le_of_P_lt h)
          have hdc : Desc c := isNF1_desc (isNF1_arg hy.nf)
          have hdc' : Desc c' := isNF1_desc (isNF1_arg hy'.nf)
          simp only [omegaArg]
          by_cases hU : uncPart c = Z
          · rw [if_pos hU]
            by_cases hU' : uncPart c' = Z
            · rw [if_pos hU']; exact h
            · rw [if_neg hU']
              split
              · exact lt_unc_add (unc_uncPart c') hU' b' (Or.inr ⟨c, b, rfl⟩)
              · exact lt_unc_add (unc_uncPart c') hU' _ (Or.inr ⟨c, b, rfl⟩)
          · have hU' := uncPart_ne_of_le hU hcc
            rw [if_neg hU, if_neg hU']
            have hcU := uncPart_add_cntPart c
            have hcU' := uncPart_add_cntPart c'
            have hbcnt : b = Z ∨ ∃ a e, b = P 0 a e := cnt_head_of_cnt hy.cnt.tail
            by_cases hUU : uncPart c = uncPart c'
            · rcases hcc with hcc | hcc
              · -- c < c'
                have hRR : cntPart c < cntPart c' := by
                  rw [← hcU, ← hcU', hUU] at hcc
                  exact (add_lt_add_left_iff _).mp hcc
                have hR'0 : cntPart c' ≠ Z := fun e => not_lt_Z' _ (e ▸ hRR)
                rw [if_neg hR'0, hUU]
                split
                · apply (add_lt_add_left_iff _).mpr
                  rcases hbcnt with rfl | ⟨a, e, rfl⟩
                  · exact Z_lt_P' _ _ _
                  · exact P_lt_P_of_head_lt _ _
                      (lt_of_le_of_lt' hy.desc.hd (T.Lt.p_mid _ _ _ _ _ hcc))
                · exact (add_lt_add_left_iff _).mpr (T.Lt.p_mid _ _ _ _ _ hcc)
              · subst hcc
                have hbb : b < b' := lt_tail h
                split
                · exact (add_lt_add_left_iff _).mpr hbb
                · exact (add_lt_add_left_iff _).mpr (T.Lt.p_tail _ _ _ _ hbb)
            · have hcc' : c < c' := by
                rcases hcc with hcc | hcc
                · exact hcc
                · subst hcc; exact absurd rfl hUU
              have hlt : T.add (uncPart c) (cntPart c) < T.add (uncPart c') (cntPart c') := by
                rw [hcU, hcU']; exact hcc'
              split
              · split
                · exact unc_add_lt (unc_uncPart c) (unc_uncPart c') (cntPart_head c)
                    (cntPart_head c') hbcnt hUU hlt
                · exact unc_add_lt (unc_uncPart c) (unc_uncPart c') (cntPart_head c)
                    (cntPart_head c') hbcnt hUU hlt
              · split
                · exact unc_add_lt (unc_uncPart c) (unc_uncPart c') (cntPart_head c)
                    (cntPart_head c') (Or.inr ⟨c, b, rfl⟩) hUU hlt
                · exact unc_add_lt (unc_uncPart c) (unc_uncPart c') (cntPart_head c)
                    (cntPart_head c') (Or.inr ⟨c, b, rfl⟩) hUU hlt

theorem omegaPow_lt_omegaPow {y y' : T} (hy : Good y) (hy' : Good y') (h : y < y') :
    omegaPow y < omegaPow y' := by
  rw [omegaPow_eq, omegaPow_eq]
  exact T.Lt.p_mid _ _ _ _ _ (omegaArg_lt hy hy' h)

theorem omegaPow_le_omegaPow {y y' : T} (hy : Good y) (hy' : Good y') (h : y ≤ y') :
    omegaPow y ≤ omegaPow y' := by
  rcases h with h | rfl
  · exact Or.inl (omegaPow_lt_omegaPow hy hy' h)
  · exact le_refl' _

theorem lastS_unc {U : T} (hU : Unc U) (hU0 : U ≠ Z) : ∀ a, P 0 a Z < lastS U := by
  intro a
  induction U with
  | Z => exact absurd rfl hU0
  | P i c d _ ihd =>
      cases d with
      | Z => exact T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hU.1)
      | P j e f => rw [lastS_P_P]; exact ihd hU.2 (by intro h; cases h)

theorem head_cnt_le_lastS {U b : T} (hU : Unc U) (hU0 : U ≠ Z) (hb : Cnt b) :
    T.head b ≤ lastS U := by
  rcases cnt_head_of_cnt hb with rfl | ⟨a, e, rfl⟩
  · exact Z_le' _
  · exact Or.inl (lastS_unc hU hU0 a)

theorem good_omegaPow {y : T} (h : Good y) : Good (omegaPow y) := by
  rw [omegaPow_eq]
  refine ⟨?_, rfl, trivial⟩
  cases y with
  | Z => exact good_one.nf
  | P i c b =>
      have hi := h.idx
      subst hi
      have hyn := h.nf
      have hcn := isNF1_arg hyn
      have hG := isNF1_G hyn
      have hcomps := comps_le_head_arg hyn
      have hcU := uncPart_add_cntPart c
      simp only [omegaArg]
      split
      · rename_i hU
        refine (isNF1_P_Z_iff 0 _).mpr ⟨hyn, ?_⟩
        intro x hx
        refine lt_of_le_of_lt' (hcomps x hx) ?_
        cases c with
        | Z => exact Z_lt_P' _ _ _
        | P j c1 c2 =>
            cases j with
            | succ j => simp only [uncPart] at hU; cases hU
            | zero => exact T.Lt.p_mid _ _ _ _ _ (hG c1 (by rw [G1_P0]; simp))
      · rename_i hU
        have hUn : T.isNF1 (uncPart c) := by
          rw [← hcU] at hcn; exact isNF1_of_add_left hcn
        split
        · rename_i hR
          have hcU' : c = uncPart c := by
            have := hcU; rw [hR, T.add_Z] at this; exact this.symm
          refine (isNF1_P_Z_iff 0 _).mpr ⟨?_, ?_⟩
          · exact isNF1_add hUn (isNF1_tail hyn)
              (head_cnt_le_lastS (unc_uncPart c) hU h.cnt.tail)
          · intro x hx
            rw [G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · rw [← hcU'] at hx
              exact lt_of_lt_of_le' (hG x hx) (by rw [← hcU']; exact le_add_right' _ _)
            · have hb0 : b ≠ Z := by intro e; subst e; exact absurd hx List.not_mem_nil
              have hxc : x ≤ c := hcomps x (by rw [G1_P0]; simp [hx])
              rw [hcU'] at hxc
              exact lt_of_le_of_lt' hxc (lt_add_of_ne _ hb0)
        · rename_i hR
          have hcA : c < T.add (uncPart c) (P 0 c b) := by
            conv => lhs; rw [← hcU]
            apply (add_lt_add_left_iff _).mpr
            rcases cntPart_head c with hR0 | ⟨r, r2, hr⟩
            · exact absurd hR0 hR
            · rw [hr]
              apply T.Lt.p_mid
              apply hG r
              rw [← hcU, G1_add, hr, G1_P0]
              simp
          refine (isNF1_P_Z_iff 0 _).mpr ⟨?_, ?_⟩
          · exact isNF1_add hUn hyn (Or.inl (lastS_unc (unc_uncPart c) hU c))
          · intro x hx
            rw [G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · have hxc : x ∈ T.G1 0 c := by rw [← hcU, G1_add]; exact List.mem_append_left _ hx
              exact lt_tr (hG x hxc) hcA
            · exact lt_of_le_of_lt' (hcomps x hx) hcA

/-! ### Cantor normal forms (level `0`) -/

theorem good_cantorT : ∀ {w : List T}, (∀ x ∈ w, Good x) →
    List.Pairwise (fun x y : T => y < x ∨ y = x) w → Good (cantorT w)
  | [], _, _ => good_Z
  | b :: bs, hw, hp => by
      simp only [cantorT]
      exact good_oadd (good_omegaPow (hw b List.mem_cons_self))
        (good_cantorT (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (List.pairwise_cons.mp hp).2)

theorem cantorT_cons : ∀ {b : T} {bs : List T}, (∀ x ∈ b :: bs, Good x) →
    List.Pairwise (fun x y : T => y < x ∨ y = x) (b :: bs) →
    cantorT (b :: bs) = P 0 (omegaArg b) (cantorT bs)
  | b, [], _, _ => by
      show oadd (omegaPow b) Z = _
      rw [oadd_Z_right, omegaPow_eq]; rfl
  | b, b' :: bs', hw, hp => by
      have ih := cantorT_cons (b := b') (bs := bs') (fun x hx => hw x (List.mem_cons_of_mem _ hx))
        (List.pairwise_cons.mp hp).2
      show oadd (omegaPow b) (cantorT (b' :: bs')) = _
      rw [ih, omegaPow_eq, oadd_P_of_not_lt, oadd_Z_left]
      show ¬ P 0 (omegaArg b) Z < P 0 (omegaArg b') Z
      apply not_lt_of_le'
      have hbb : b' ≤ b := by
        rcases (List.pairwise_cons.mp hp).1 b' List.mem_cons_self with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hle := omegaPow_le_omegaPow (hw b' (by simp)) (hw b List.mem_cons_self) hbb
      rwa [omegaPow_eq, omegaPow_eq] at hle

theorem cantorT_lt : ∀ {s t : List T}, (∀ x ∈ s, Good x) → (∀ x ∈ t, Good x) →
    List.Pairwise (fun x y : T => y < x ∨ y = x) s →
    List.Pairwise (fun x y : T => y < x ∨ y = x) t → s < t → cantorT s < cantorT t
  | [], [], _, _, _, _, h => absurd h List.not_lex_nil
  | [], b :: t, _, ht, _, hpt, _ => by
      rw [cantorT_cons ht hpt]; exact Z_lt_P' _ _ _
  | _ :: _, [], _, _, _, _, h => absurd h List.not_lex_nil
  | a :: s, b :: t, hs, ht, hps, hpt, h => by
      rw [cantorT_cons hs hps, cantorT_cons ht hpt]
      cases h with
      | rel h =>
          exact T.Lt.p_mid _ _ _ _ _
            (omegaArg_lt (hs a List.mem_cons_self) (ht b List.mem_cons_self) h)
      | cons h =>
          exact T.Lt.p_tail _ _ _ _
            (cantorT_lt (fun x hx => hs x (List.mem_cons_of_mem _ hx))
              (fun x hx => ht x (List.mem_cons_of_mem _ hx))
              (List.pairwise_cons.mp hps).2 (List.pairwise_cons.mp hpt).2 h)

end Sem
