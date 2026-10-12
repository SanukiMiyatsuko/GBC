import Mbekworm.Sequence.SemArith

/-!
# The Veblen-type functions `phi k a ξ`
-/

open T

namespace Sem

/-- A summand lies at level `≥ k`. -/
def BigK (k : Nat) (i : Nat) (c : T) : Prop := 2 ≤ i ∨ (1 ≤ i ∧ copies Om k ≤ c)

/-- All summands lie at level `≥ k`. -/
def AllBigK (k : Nat) : T → Prop
  | Z => True
  | P i c b => BigK k i c ∧ AllBigK k b

/-- Principal terms `ψ₀(Y)` whose argument lies at level `≥ k`. -/
def Lvl (k : Nat) (Φ : T) : Prop := ∃ Y, Φ = P 0 Y Z ∧ Y ≠ Z ∧ AllBigK k Y

theorem Lvl.ne_Z {k : Nat} {Φ : T} (h : Lvl k Φ) : Φ ≠ Z := by
  obtain ⟨Y, rfl, -, -⟩ := h; intro e; cases e

/-! ### Prefixes and components -/

theorem size_add_ge : ∀ (U r : T), U.size ≤ (T.add U r).size
  | Z, r => Nat.zero_le _
  | P i a b, r => by
      rw [add_P, T.size_P, T.size_P]
      have := size_add_ge b r
      omega

/-- Anything between `U` and `U ++ R` extends `U`. -/
theorem between_prefix : ∀ {U x R : T}, U ≤ x → x < T.add U R → ∃ r, x = T.add U r
  | Z, x, _, _, _ => ⟨x, rfl⟩
  | P i a b, x, R, h₁, h₂ => by
      rw [add_P] at h₂
      cases x with
      | Z =>
          rcases h₁ with h | h
          · exact absurd h (not_lt_Z' _)
          · cases h
      | P j c d =>
          rcases h₁ with h | h
          · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
            · rcases lt_inv _ _ _ _ _ _ h₂ with h'' | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
              · exfalso; omega
              · exfalso; omega
              · exfalso; omega
            · rcases lt_inv _ _ _ _ _ _ h₂ with h'' | ⟨_, h''⟩ | ⟨_, rfl, _⟩
              · exfalso; omega
              · exact absurd (lt_tr h' h'') (lt_irr _)
              · exact absurd h' (lt_irr _)
            · rcases lt_inv _ _ _ _ _ _ h₂ with h'' | ⟨_, h''⟩ | ⟨_, _, h''⟩
              · exfalso; omega
              · exact absurd h'' (lt_irr _)
              · obtain ⟨r, hr⟩ := between_prefix (Or.inl h') h''
                exact ⟨r, by rw [add_P, hr]⟩
          · injection h with h1 h2 h3
            subst h1 h2 h3
            exact ⟨Z, by rw [T.add_Z]⟩

/-- A component of `U` that is below `U ++ R` is below `U`. -/
theorem lt_prefix_of_comp {u : Nat} {U x R : T} (hx : x ∈ T.G1 u U) (h : x < T.add U R) : x < U := by
  rcases lt_total_thm x U with h' | h' | h'
  · exact h'
  · obtain ⟨r, rfl⟩ := between_prefix (Or.inl h') h
    have := G1_size_lt u U _ hx
    have := size_add_ge U r
    exfalso; omega
  · subst h'
    have := G1_size_lt u x x hx
    exfalso; omega

/-- The uncountable part of a principal normal form is itself principal. -/
theorem isNF1_psi_unc {c : T} (hc : T.isNF1 (P 0 c Z)) : T.isNF1 (P 0 (uncPart c) Z) := by
  have hcU := uncPart_add_cntPart c
  have hcn := isNF1_arg hc
  rw [← hcU] at hcn
  refine (isNF1_P_Z_iff 0 _).mpr ⟨isNF1_of_add_left hcn, ?_⟩
  intro x hx
  apply lt_prefix_of_comp hx (R := cntPart c)
  rw [hcU]
  apply isNF1_G hc
  rw [← hcU, G1_add]
  exact List.mem_append_left _ hx

theorem Desc.cnt_cntPart : ∀ {c : T}, Desc c → Cnt (cntPart c)
  | Z, _ => trivial
  | P 0 a b, h => by
      show Cnt (P 0 a b)
      refine ⟨rfl, ?_⟩
      have hb := h.tail
      have hhd := h.hd
      clear h
      induction b with
      | Z => trivial
      | P j e f _ ih =>
          have hj : j = 0 := by
            rcases hhd with h' | h'
            · rcases lt_inv _ _ _ _ _ _ h' with h'' | ⟨_, _⟩ | ⟨_, _, _⟩
              · omega
              · assumption
              · assumption
            · simp only [T.head] at h'; injection h' with h''
          subst hj
          exact ⟨rfl, ih hb.tail (le_tr hb.hd (by
            rcases hhd with h' | h'
            · exact Or.inl h'
            · exact Or.inr h'))⟩
  | P (i + 1) a b, h => by
      show Cnt (cntPart b)
      exact Desc.cnt_cntPart h.tail

theorem good_logA {c : T} (hc : T.isNF1 (P 0 c Z)) : Good (logA c) := by
  have hcn := isNF1_arg hc
  have hdc := isNF1_desc hcn
  have hcU := uncPart_add_cntPart c
  unfold logA
  split
  · rename_i hU
    refine ⟨hcn, ?_⟩
    have := hdc.cnt_cntPart
    have e : cntPart c = c := by
      have h2 := hcU; rw [hU] at h2; exact h2
    rwa [e] at this
  · have hR : T.isNF1 (cntPart c) := by rw [← hcU] at hcn; exact isNF1_of_add_right hcn
    exact good_oadd ⟨isNF1_psi_unc hc, rfl, trivial⟩ ⟨hR, hdc.cnt_cntPart⟩

theorem head_le_logA {c : T} (hU : uncPart c ≠ Z) : P 0 (uncPart c) Z ≤ T.head (logA c) := by
  unfold logA
  rw [if_neg hU]
  exact head_oadd_le (P 0 (uncPart c) Z) (cntPart c)

theorem Om_le_of_unc {U : T} (hU : Unc U) (hU0 : U ≠ Z) : Om ≤ U := by
  cases U with
  | Z => exact absurd rfl hU0
  | P i a b =>
      rcases Nat.lt_or_ge 1 i with h | h
      · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h)
      · have hi : i = 1 := by have := hU.1; omega
        subst hi
        cases a with
        | Z =>
            cases b with
            | Z => exact le_refl' _
            | P _ _ _ => exact Or.inl (T.Lt.p_tail _ _ _ _ (Z_lt_P' _ _ _))
        | P _ _ _ => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _))

/-- A countable principal normal form is below `ε₀`. -/
theorem cnt_arg_lt_eps {c : T} (hc : T.isNF1 (P 0 c Z)) (hU : uncPart c = Z) :
    c < P 0 Om Z := by
  cases c with
  | Z => exact Z_lt_P' _ _ _
  | P i c1 c2 =>
      cases i with
      | succ i => simp only [uncPart] at hU; cases hU
      | zero =>
          apply P_lt_P_of_head_lt
          apply T.Lt.p_mid
          have h1 : c1 < P 0 c1 c2 := isNF1_G hc c1 (by rw [G1_P0]; simp)
          exact lt_tr h1 (T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one)

theorem head_lt_of_lt_single {x : T} {j : Nat} {c : T} (h : x < P j c Z) : T.head x < P j c Z := by
  cases x with
  | Z => exact Z_lt_P' _ _ _
  | P i a b =>
      rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
      · exact T.Lt.p_head _ _ _ _ _ _ h'
      · exact T.Lt.p_mid _ _ _ _ _ h'
      · exact absurd h' (not_lt_Z' _)

theorem head_oadd_cases (x y : T) : T.head (oadd x y) = T.head x ∨ T.head (oadd x y) = T.head y := by
  cases x with
  | Z => exact Or.inr rfl
  | P i a b =>
      rw [oadd_P]
      split
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem logA_of_unc_Z {c : T} (hU : uncPart c = Z) : logA c = c := by
  unfold logA; rw [if_pos hU]

theorem logA_of_unc_ne {c : T} (hU : uncPart c ≠ Z) :
    logA c = oadd (P 0 (uncPart c) Z) (cntPart c) := by
  unfold logA; rw [if_neg hU]

theorem logA_lt_logA {c d : T} (hc : T.isNF1 (P 0 c Z)) (hd : T.isNF1 (P 0 d Z)) (h : c < d) :
    logA c < logA d := by
  have hcU := uncPart_add_cntPart c
  have hdU := uncPart_add_cntPart d
  by_cases hU : uncPart c = Z
  · rw [logA_of_unc_Z hU]
    by_cases hU' : uncPart d = Z
    · rw [logA_of_unc_Z hU']; exact h
    · apply lt_of_head_lt
      refine lt_of_lt_of_le' ?_ (head_le_logA hU')
      apply head_lt_of_lt_single
      exact lt_of_lt_of_le' (cnt_arg_lt_eps hc hU)
        (P0_le_P0_iff.mpr (Om_le_of_unc (unc_uncPart d) hU'))
  · have hU' := uncPart_ne_of_le hU (le_of_lt' h)
    rw [logA_of_unc_ne hU, logA_of_unc_ne hU']
    by_cases hUU : uncPart c = uncPart d
    · rw [hUU]
      apply oadd_lt_oadd_right (Desc.single 0 _)
      rw [← hcU, ← hdU, hUU] at h
      exact (add_lt_add_left_iff _).mp h
    · have hlt : T.add (uncPart c) (cntPart c) < T.add (uncPart d) (cntPart d) := by
        rw [hcU, hdU]; exact h
      have hUlt : uncPart c < uncPart d := by
        have := unc_add_lt (S := Z) (S' := Z) (unc_uncPart c) (unc_uncPart d) (cntPart_head c)
          (cntPart_head d) (Or.inl rfl) hUU hlt
        rwa [T.add_Z, T.add_Z] at this
      have hcd : c < uncPart d := by
        have := unc_add_lt (S := cntPart c) (S' := Z) (unc_uncPart c) (unc_uncPart d)
          (cntPart_head c) (cntPart_head d) (cntPart_head c) hUU hlt
        rwa [hcU, T.add_Z] at this
      apply lt_of_head_lt
      refine lt_of_lt_of_le' ?_ (head_oadd_le (P 0 (uncPart d) Z) (cntPart d))
      rcases head_oadd_cases (P 0 (uncPart c) Z) (cntPart c) with e | e
      · rw [e]; exact T.Lt.p_mid _ _ _ _ _ hUlt
      · rw [e]
        rcases cntPart_head c with hR | ⟨r, r2, hr⟩
        · rw [hR]; exact Z_lt_P' _ _ _
        · rw [hr]
          apply T.Lt.p_mid
          have hrc : r < c := by
            apply isNF1_G hc r
            rw [← hcU, G1_add, hr, G1_P0]
            simp
          exact lt_tr hrc hcd

/-! ### `copies`, levels and `Unc` -/

theorem copies_add (x : T) : ∀ j d : Nat, copies x (j + d) = T.add (copies x j) (copies x d)
  | 0, d => by simp [copies]; rfl
  | j + 1, d => by
      rw [show j + 1 + d = (j + d) + 1 by omega]
      show P 1 x (copies x (j + d)) = T.add (P 1 x (copies x j)) (copies x d)
      rw [add_P, copies_add x j d]

theorem copies_le (x : T) {j k : Nat} (h : j ≤ k) : copies x j ≤ copies x k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [copies_add]
  exact le_add_right' _ _

theorem BigK.mono {k j i : Nat} {c : T} (h : BigK k i c) (hjk : j ≤ k) : BigK j i c := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, le_tr (copies_le Om hjk) h2⟩

theorem AllBigK.mono {k j : Nat} : ∀ {Y : T}, AllBigK k Y → j ≤ k → AllBigK j Y
  | Z, _, _ => trivial
  | P _ _ _, h, hjk => ⟨h.1.mono hjk, AllBigK.mono h.2 hjk⟩

theorem AllBigK.unc {k : Nat} : ∀ {Y : T}, AllBigK k Y → Unc Y
  | Z, _ => trivial
  | P i _ _, h => ⟨by rcases h.1 with h1 | ⟨h1, _⟩ <;> omega, AllBigK.unc h.2⟩

theorem AllBigK.add {k : Nat} : ∀ {X Y : T}, AllBigK k X → AllBigK k Y → AllBigK k (T.add X Y)
  | Z, _, _, hY => hY
  | P _ _ _, _, hX, hY => by rw [add_P]; exact ⟨hX.1, AllBigK.add hX.2 hY⟩

theorem Unc.uncPart : ∀ {Y : T}, Unc Y → uncPart Y = Y
  | Z, _ => rfl
  | P 0 _ _, h => absurd h.1 (by omega)
  | P (i + 1) a b, h => by
      show P (i + 1) a (Sem.uncPart b) = P (i + 1) a b
      rw [Unc.uncPart h.2]

theorem Unc.cntPart : ∀ {Y : T}, Unc Y → cntPart Y = Z
  | Z, _ => rfl
  | P 0 _ _, h => absurd h.1 (by omega)
  | P (i + 1) _ b, h => by
      show Sem.cntPart b = Z
      exact Unc.cntPart h.2

theorem Unc.add : ∀ {X Y : T}, Unc X → Unc Y → Unc (T.add X Y)
  | Z, _, _, hY => hY
  | P _ _ _, _, hX, hY => by rw [add_P]; exact ⟨hX.1, Unc.add hX.2 hY⟩

theorem Lvl.minus1 {k : Nat} {Φ : T} (h : Lvl k Φ) : minus1 Φ = Φ := by
  obtain ⟨Y, rfl, hY, -⟩ := h
  cases Y with
  | Z => exact absurd rfl hY
  | P _ _ _ => rfl

theorem Lvl.omegaPow {k : Nat} {Φ : T} (h : Lvl k Φ) : omegaPow Φ = Φ := by
  obtain ⟨Y, rfl, hY, hb⟩ := h
  have hu := hb.unc
  show (if uncPart Y = Z then _ else if cntPart Y = Z then P 0 (T.add (uncPart Y) Z) Z else _) = _
  rw [hu.uncPart, if_neg hY, if_pos hu.cntPart, T.add_Z]

theorem Lvl.logA {k : Nat} {Y : T} (h : Lvl k (P 0 Y Z)) : logA Y = P 0 Y Z := by
  obtain ⟨Y', he, hY, hb⟩ := h
  injection he with _ he
  subst he
  have hu := hb.unc
  unfold Sem.logA
  rw [hu.uncPart, if_neg hY, hu.cntPart, oadd_Z_right]

/-! ### Prefixes cut out by a predicate -/

/-- The remainder after `takeW p`. -/
def dropW (p : Nat → T → Bool) : T → T
  | Z => Z
  | P i a b => if p i a then dropW p b else P i a b

theorem takeW_add_dropW (p : Nat → T → Bool) : ∀ x : T, T.add (takeW p x) (dropW p x) = x
  | Z => rfl
  | P i a b => by
      simp only [takeW, dropW]
      split
      · rw [add_P, takeW_add_dropW p b]
      · rfl

theorem dropW_head (p : Nat → T → Bool) : ∀ x : T,
    dropW p x = Z ∨ ∃ i a b, dropW p x = P i a b ∧ p i a = false
  | Z => Or.inl rfl
  | P i a b => by
      simp only [dropW]
      split
      · exact dropW_head p b
      · rename_i h; exact Or.inr ⟨i, a, b, rfl, by simpa using h⟩

/-- All summands satisfy a predicate. -/
def AllW (p : Nat → T → Bool) : T → Prop
  | Z => True
  | P i a b => p i a = true ∧ AllW p b

theorem takeW_all (p : Nat → T → Bool) : ∀ x : T, AllW p (takeW p x)
  | Z => trivial
  | P i a b => by
      simp only [takeW]
      split
      · rename_i h; exact ⟨h, takeW_all p b⟩
      · trivial

theorem takeW_of_all (p : Nat → T → Bool) : ∀ x : T, AllW p x → takeW p x = x
  | Z, _ => rfl
  | P i a b, h => by simp only [takeW, if_pos h.1, takeW_of_all p b h.2]

/-- Upward closed summand predicates. -/
def UpW (p : Nat → T → Bool) : Prop := ∀ i a j c, p i a = true → P i a Z ≤ P j c Z → p j c = true

theorem takeW_le_takeW {p : Nat → T → Bool} (hp : UpW p) : ∀ {x y : T}, x ≤ y → takeW p x ≤ takeW p y
  | Z, _, _ => Z_le' _
  | P i a b, Z, h => by
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i a b, P j c d, h => by
      simp only [takeW]
      by_cases hpa : p i a = true
      · rw [if_pos hpa]
        rcases h with h | h
        · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
          · rw [if_pos (hp i a j c hpa (Or.inl (T.Lt.p_head _ _ _ _ _ _ h')))]
            exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h')
          · rw [if_pos (hp i a i c hpa (Or.inl (T.Lt.p_mid _ _ _ _ _ h')))]
            exact Or.inl (T.Lt.p_mid _ _ _ _ _ h')
          · rw [if_pos hpa]
            exact P_le_P_tail (takeW_le_takeW hp (Or.inl h'))
        · injection h with h1 h2 h3; subst h1 h2 h3
          rw [if_pos hpa]; exact le_refl' _
      · rw [if_neg hpa]; exact Z_le' _

theorem takeW_prefix_le (p : Nat → T → Bool) (x : T) : takeW p x ≤ x := by
  conv => rhs; rw [← takeW_add_dropW p x]
  exact le_add_right' _ _

/-! ### `omegaTimes`, `OG` and `OPowTimes` -/

theorem omegaTimes_add : ∀ x y : T, omegaTimes (T.add x y) = T.add (omegaTimes x) (omegaTimes y)
  | Z, _ => rfl
  | P i c b, y => by
      rw [add_P]
      show P 1 (logA c) (omegaTimes (T.add b y)) = T.add (P 1 (logA c) (omegaTimes b)) (omegaTimes y)
      rw [add_P, omegaTimes_add b y]

theorem unc_omegaTimes : ∀ x : T, Unc (omegaTimes x)
  | Z => trivial
  | P _ _ b => ⟨Nat.le_refl 1, unc_omegaTimes b⟩

theorem unc_copies (x : T) : ∀ k : Nat, Unc (copies x k)
  | 0 => trivial
  | k + 1 => ⟨Nat.le_refl 1, unc_copies x k⟩

theorem unc_OG (k : Nat) (a : T) : Unc (OG k a) := Unc.add (unc_copies Om k) (unc_omegaTimes a)

theorem OG_ne_Z {k : Nat} {a : T} (hk : k = 0 → a ≠ Z) : OG k a ≠ Z := by
  intro h
  have h' := (add_eq_Z_iff.mp h)
  cases k with
  | zero =>
      cases a with
      | Z => exact hk rfl rfl
      | P _ _ _ => exact absurd h'.2 nofun
  | succ k => exact absurd h'.1 nofun

theorem dropOm_P_ne {i : Nat} {a b : T} (h : ¬ (i = 1 ∧ a = Z)) : dropOm (P i a b) = P i a b := by
  unfold dropOm
  split
  · rename_i heq
    injection heq with h1 h2
    exact absurd ⟨h1, h2⟩ h
  · rfl

theorem dropOm_add_of_cnt {G y : T} (hG : Unc G) (hy : Cnt y) :
    dropOm (T.add G y) = T.add (dropOm G) y := by
  cases G with
  | Z =>
      cases y with
      | Z => rfl
      | P i a b =>
          rw [hy.idx]
          show dropOm (P 0 a b) = P 0 a b
          exact dropOm_P_ne (by omega)
  | P i a b =>
      rw [add_P]
      by_cases h : i = 1 ∧ a = Z
      · obtain ⟨rfl, rfl⟩ := h; rfl
      · rw [dropOm_P_ne h, dropOm_P_ne h, add_P]

/-- The exponent part shared by the summands of `OPowTimes k a`. -/
def OGd (k : Nat) (a : T) : T := dropOm (OG k a)

theorem OPowTimes_P (k : Nat) (a : T) (i : Nat) (c b : T) (hc : Cnt (logA c)) :
    OPowTimes k a (P i c b) = P 1 (T.add (OGd k a) (logA c)) (OPowTimes k a b) := by
  show P 1 (dropOm (T.add (OG k a) (logA c))) (OPowTimes k a b) = _
  rw [dropOm_add_of_cnt (unc_OG k a) hc]; rfl

theorem OPowTimes_Z (k : Nat) (a : T) : OPowTimes k a Z = Z := rfl

theorem OPowTimes_ne_Z {k : Nat} {a X : T} (hX : X ≠ Z) : OPowTimes k a X ≠ Z := by
  cases X with
  | Z => exact absurd rfl hX
  | P _ _ _ => intro e; cases e

theorem cnt_logA_of_good {i : Nat} {c b : T} (h : Good (P i c b)) : Cnt (logA c) := by
  have hi := h.idx; subst hi
  exact (good_logA (isNF1_head h.nf)).cnt

/-- `OPowTimes` is strictly monotone in its countable argument. -/
theorem OPowTimes_lt (k : Nat) (a : T) : ∀ {X X' : T}, Good X → Good X' → X < X' →
    OPowTimes k a X < OPowTimes k a X'
  | Z, Z, _, _, h => absurd h (not_lt_Z' _)
  | Z, P _ _ _, _, _, _ => Z_lt_P' _ _ _
  | P _ _ _, Z, _, _, h => absurd h (not_lt_Z' _)
  | P i c b, P j d e, hX, hX', h => by
      rw [OPowTimes_P k a i c b (cnt_logA_of_good hX), OPowTimes_P k a j d e (cnt_logA_of_good hX')]
      have hi := hX.idx; have hj := hX'.idx; subst hi hj
      rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, rfl, h'⟩
      · exact absurd h' (Nat.lt_irrefl _)
      · exact T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr
          (logA_lt_logA (isNF1_head hX.nf) (isNF1_head hX'.nf) h'))
      · exact T.Lt.p_tail _ _ _ _ (OPowTimes_lt k a hX.tail hX'.tail h')

theorem OPowTimes_le (k : Nat) (a : T) {X X' : T} (hX : Good X) (hX' : Good X') (h : X ≤ X') :
    OPowTimes k a X ≤ OPowTimes k a X' := by
  rcases h with h | rfl
  · exact Or.inl (OPowTimes_lt k a hX hX' h)
  · exact le_refl' _

theorem good_onePlus {ξ : T} (h : Good ξ) : Good (onePlus ξ) := by
  cases ξ with
  | Z => exact good_one
  | P i a b =>
      have hi := h.idx; subst hi
      cases a with
      | Z =>
          refine ⟨(isNF1_P_iff 0 Z _).mpr ⟨good_one.nf, h.nf, ?_⟩, rfl, h.cnt⟩
          exact le_refl' _
      | P _ _ _ => exact h

theorem onePlus_ne_Z (ξ : T) : onePlus ξ ≠ Z := by
  cases ξ with
  | Z => intro e; cases e
  | P i a b =>
      cases i with
      | succ i => intro e; cases e
      | zero => cases a with
        | Z => intro e; cases e
        | P _ _ _ => intro e; cases e

/-! ### Exponents, thresholds and the predicates of `phi` -/

theorem logA_le_logA {c d : T} (hc : T.isNF1 (P 0 c Z)) (hd : T.isNF1 (P 0 d Z)) (h : c ≤ d) :
    logA c ≤ logA d := by
  rcases h with h | rfl
  · exact Or.inl (logA_lt_logA hc hd h)
  · exact le_refl' _

theorem desc_omegaTimes : ∀ {a : T}, Good a → Desc (omegaTimes a)
  | Z, _ => trivial
  | P i c b, ha => by
      show Desc (P 1 (logA c) (omegaTimes b))
      refine ⟨?_, desc_omegaTimes ha.tail⟩
      cases b with
      | Z => exact Z_le' _
      | P j c' b' =>
          show P 1 (logA c') Z ≤ P 1 (logA c) Z
          have hi := ha.idx; subst hi
          have hj := ha.tail.idx; subst hj
          have hcc : c' ≤ c := P0_le_P0_iff.mp ha.desc.hd
          rcases logA_le_logA (isNF1_head ha.tail.nf) (isNF1_head ha.nf) hcc with h | h
          · exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
          · rw [h]; exact le_refl' _

theorem desc_copies (x : T) : ∀ k : Nat, Desc (copies x k)
  | 0 => trivial
  | k + 1 => by
      show Desc (P 1 x (copies x k))
      refine ⟨?_, desc_copies x k⟩
      cases k with
      | zero => exact Z_le' _
      | succ k => exact le_refl' _

theorem lastS_copies (x : T) : ∀ k : Nat, lastS (copies x (k + 1)) = P 1 x Z
  | 0 => rfl
  | k + 1 => by
      show lastS (P 1 x (P 1 x (copies x k))) = P 1 x Z
      rw [lastS_P_P]; exact lastS_copies x k

theorem desc_OG (k : Nat) {a : T} (ha : Good a) : Desc (OG k a) := by
  apply Desc.add (desc_copies Om k) (desc_omegaTimes ha)
  intro i b c he
  cases k with
  | zero => cases he
  | succ k =>
      rw [lastS_copies]
      cases a with
      | Z => exact Z_le' _
      | P j e f =>
          show P 1 (logA e) Z ≤ P 1 Om Z
          have hj := ha.idx; subst hj
          exact Or.inl (T.Lt.p_mid _ _ _ _ _ (Cnt_lt_Om (good_logA (isNF1_head ha.nf)).cnt))

theorem Om_le_lastS : ∀ {G : T}, Unc G → G ≠ Z → Om ≤ lastS G
  | Z, _, h => absurd rfl h
  | P i a Z, hG, _ => Om_le_of_unc hG nofun
  | P i a (P j c d), hG, _ => by rw [lastS_P_P]; exact Om_le_lastS hG.2 nofun

theorem thr_eq (k : Nat) {a : T} (ha : Good a) : oadd (OG k a) Om = T.add (OG k a) Om := by
  by_cases h0 : OG k a = Z
  · rw [h0]; rfl
  · exact oadd_eq_add (desc_OG k ha) (Om_le_lastS (unc_OG k a) h0)

theorem exp_OGd {k : Nat} {a lam : T} (ha : Good a) (h0 : OG k a ≠ Z) (hlam : Cnt lam) :
    oadd Om (T.add (OGd k a) lam) = T.add (OG k a) lam := by
  have hd := desc_OG k ha
  have hu := unc_OG k a
  unfold OGd
  generalize OG k a = G at hd hu h0 ⊢
  cases G with
  | Z => exact absurd rfl h0
  | P i x r =>
      by_cases hh : i = 1 ∧ x = Z
      · obtain ⟨rfl, rfl⟩ := hh
        show oadd (P 1 Z Z) (T.add r lam) = T.add (P 1 Z r) lam
        rw [add_P, oadd_P_of_not_lt, oadd_Z_left]
        apply not_lt_of_le'
        cases r with
        | Z =>
            rcases cnt_head_of_cnt hlam with rfl | ⟨a', b', rfl⟩
            · exact Z_le' _
            · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one)
        | P j c d => rw [add_P]; exact hd.hd
      · rw [dropOm_P_ne hh, add_P]
        apply oadd_P_of_lt
        show P 1 Z Z < P i x Z
        rcases Nat.lt_or_ge 1 i with h1 | h1
        · exact T.Lt.p_head _ _ _ _ _ _ h1
        · have : i = 1 := by have := hu.1; omega
          subst this
          apply T.Lt.p_mid
          cases x with
          | Z => exact absurd ⟨rfl, rfl⟩ hh
          | P _ _ _ => exact Z_lt_P' _ _ _

theorem copies_le_OGd (k : Nat) (a : T) : copies Om k ≤ OGd k a := by
  cases k with
  | zero => exact Z_le' _
  | succ k =>
      unfold OGd OG
      rw [show copies Om (k + 1) = P 1 Om (copies Om k) from rfl, add_P,
        dropOm_P_ne (by intro h; cases h.2), ← add_P]
      exact le_add_right' _ _

theorem thr_lt_copies (k : Nat) {a : T} (ha : Good a) : oadd (OG k a) Om < copies Om (k + 1) := by
  rw [thr_eq k ha, OG, add_assoc'', copies_add Om k 1]
  apply (add_lt_add_left_iff _).mpr
  cases a with
  | Z => exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
  | P j e f =>
      show P 1 (logA e) (T.add (omegaTimes f) Om) < P 1 Om Z
      have hj := ha.idx; subst hj
      exact T.Lt.p_mid _ _ _ _ _ (Cnt_lt_Om (good_logA (isNF1_head ha.nf)).cnt)

theorem omegaTimes_succ_le : ∀ {α β : T}, Good α → Good β → α < β →
    T.add (omegaTimes α) Om ≤ omegaTimes β
  | Z, Z, _, _, h => absurd h (not_lt_Z' _)
  | Z, P i c b, _, _, _ => by
      show P 1 Z Z ≤ P 1 (logA c) (omegaTimes b)
      cases hl : logA c with
      | Z =>
          cases omegaTimes b with
          | Z => exact le_refl' _
          | P _ _ _ => exact Or.inl (T.Lt.p_tail _ _ _ _ (Z_lt_P' _ _ _))
      | P _ _ _ => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _))
  | P _ _ _, Z, _, _, h => absurd h (not_lt_Z' _)
  | P i c b, P j c' b', hα, hβ, h => by
      show T.add (P 1 (logA c) (omegaTimes b)) Om ≤ P 1 (logA c') (omegaTimes b')
      rw [add_P]
      have hi := hα.idx; have hj := hβ.idx; subst hi hj
      rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, rfl, h'⟩
      · exact absurd h' (Nat.lt_irrefl _)
      · exact Or.inl (T.Lt.p_mid _ _ _ _ _
          (logA_lt_logA (isNF1_head hα.nf) (isNF1_head hβ.nf) h'))
      · exact P_le_P_tail (omegaTimes_succ_le hα.tail hβ.tail h')

theorem OG_succ_le (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (h : α < β) :
    T.add (OG k α) Om ≤ OG k β := by
  unfold OG
  rw [add_assoc'']
  exact (add_le_add_left_iff _).mpr (omegaTimes_succ_le hα hβ h)

/-- The predicate of `alphaHead`. -/
def predA (k : Nat) (i : Nat) (c : T) : Bool :=
  decide (2 ≤ i) || (decide (1 ≤ i) && leB (copies Om (k + 1)) c)

theorem alphaHead_P (k j : Nat) (d b : T) : alphaHead k (P j d b) = takeW (predA k) d := rfl

theorem predA_iff {k i : Nat} {c : T} : predA k i c = true ↔ BigK (k + 1) i c := by
  simp only [predA, BigK, leB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem bigW_iff {thr : T} {i : Nat} {c : T} :
    bigW thr i c = true ↔ 2 ≤ i ∨ (1 ≤ i ∧ thr ≤ oadd Om c) := by
  simp only [bigW, leB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem oadd_Om_le {c c' : T} (h : c ≤ c') : oadd Om c ≤ oadd Om c' := by
  rcases h with h | rfl
  · exact Or.inl (oadd_lt_oadd_right (Desc.single 1 Z) h)
  · exact le_refl' _

theorem lt_of_oadd_Om_lt {c c' : T} (h : oadd Om c < oadd Om c') : c < c' := by
  rcases lt_total_thm c c' with h' | h' | h'
  · exact h'
  · exact absurd h (not_lt_of_le' (oadd_Om_le (Or.inl h')))
  · subst h'; exact absurd h (lt_irr _)

theorem upW_bigW (thr : T) : UpW (bigW thr) := by
  intro i a j c hp hle
  rw [bigW_iff] at hp ⊢
  rcases hle with hle | hle
  · rcases lt_inv _ _ _ _ _ _ hle with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
    · left; rcases hp with hp | ⟨hp, _⟩ <;> omega
    · rcases hp with hp | ⟨hp1, hp2⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp1, le_tr hp2 (oadd_Om_le (Or.inl h))⟩
    · exact absurd h (not_lt_Z' _)
  · injection hle with h1 h2; subst h1 h2; exact hp

theorem upW_predA (k : Nat) : UpW (predA k) := by
  intro i a j c hp hle
  rw [predA_iff] at hp ⊢
  rcases hle with hle | hle
  · rcases lt_inv _ _ _ _ _ _ hle with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
    · left; rcases hp with hp | ⟨hp, _⟩ <;> omega
    · rcases hp with hp | ⟨hp1, hp2⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp1, le_tr hp2 (Or.inl h)⟩
    · exact absurd h (not_lt_Z' _)
  · injection hle with h1 h2; subst h1 h2; exact hp

theorem AllW.add_right {p : Nat → T → Bool} : ∀ {X r : T}, AllW p (T.add X r) → AllW p r
  | Z, _, h => h
  | P _ _ _, _, h => by rw [add_P] at h; exact AllW.add_right h.2

theorem AllW.allBigK_predA {k : Nat} : ∀ {Y : T}, AllW (predA k) Y → AllBigK (k + 1) Y
  | Z, _ => trivial
  | P _ _ _, h => ⟨predA_iff.mp h.1, AllW.allBigK_predA h.2⟩

theorem AllBigK.allW_predA {k : Nat} : ∀ {Y : T}, AllBigK (k + 1) Y → AllW (predA k) Y
  | Z, _ => trivial
  | P _ _ _, h => ⟨predA_iff.mpr h.1, AllBigK.allW_predA h.2⟩

/-- A big summand dominates `OPowTimes` summands. -/
theorem lt_big {thr e c : T} {i : Nat} (hb : bigW thr i c = true) (he : oadd Om e < thr) :
    P 1 e Z < P i c Z := by
  rcases bigW_iff.mp hb with h | ⟨_, h⟩
  · exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  · have hi : i = 1 ∨ 2 ≤ i := by omega
    rcases hi with rfl | hi
    · exact T.Lt.p_mid _ _ _ _ _ (lt_of_oadd_Om_lt (lt_of_lt_of_le' he h))
    · exact T.Lt.p_head _ _ _ _ _ _ (by omega)

/-- All summands are of the form `P 1 e Z` with exponent below `thr`. -/
def ExpBelow (thr : T) : T → Prop
  | Z => True
  | P i e b => i = 1 ∧ oadd Om e < thr ∧ ExpBelow thr b

theorem expBelow_OPowTimes (k : Nat) {a : T} (ha : Good a) (hk : k = 0 → a ≠ Z) :
    ∀ {X : T}, Good X → ExpBelow (oadd (OG k a) Om) (OPowTimes k a X)
  | Z, _ => trivial
  | P i c b, hX => by
      rw [OPowTimes_P k a i c b (cnt_logA_of_good hX)]
      refine ⟨rfl, ?_, expBelow_OPowTimes k ha hk hX.tail⟩
      rw [exp_OGd ha (OG_ne_Z hk) (cnt_logA_of_good hX), thr_eq k ha]
      exact (add_lt_add_left_iff _).mpr (Cnt_lt_Om (cnt_logA_of_good hX))

/-- `O` stays below anything starting with a big summand. -/
theorem lt_of_expBelow {thr O : T} {i : Nat} {c r : T} (hO : ExpBelow thr O)
    (hb : bigW thr i c = true) : O < P i c r := by
  cases O with
  | Z => exact Z_lt_P' _ _ _
  | P j e b =>
      obtain ⟨rfl, he, -⟩ := hO
      exact P_lt_P_of_head_lt _ _ (lt_big hb he)

/-- `Pre ++ O < D ++ W` when `D` exceeds `Pre` by big summands. -/
theorem pre_lt {thr : T} : ∀ {Pre D O : T} (W : T), Pre < D →
    (∀ r, D = T.add Pre r → AllW (bigW thr) r) → ExpBelow thr O → T.add Pre O < T.add D W
  | Z, Z, _, _, hlt, _, _ => absurd hlt (lt_irr _)
  | Z, P i c r, O, W, _, hD, hO => by
      rw [add_Z_left', add_P]
      exact lt_of_expBelow hO (hD (P i c r) rfl).1
  | P _ _ _, Z, _, _, hlt, _, _ => absurd hlt (not_lt_Z' _)
  | P i a b, P j c d, O, W, hlt, hD, hO => by
      rw [add_P, add_P]
      rcases lt_inv _ _ _ _ _ _ hlt with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
      · exact T.Lt.p_head _ _ _ _ _ _ h'
      · exact T.Lt.p_mid _ _ _ _ _ h'
      · apply T.Lt.p_tail
        exact pre_lt W h' (fun r hr => hD r (by rw [add_P, hr])) hO

theorem onePlus_lt {ξ ξ' : T} (hξ : Good ξ) (hξ' : Good ξ') (h : ξ < ξ') : onePlus ξ < onePlus ξ' := by
  cases ξ with
  | Z =>
      cases ξ' with
      | Z => exact absurd h (not_lt_Z' _)
      | P i a b =>
          have hi := hξ'.idx; subst hi
          cases a with
          | Z => exact T.Lt.p_tail _ _ _ _ (Z_lt_P' _ _ _)
          | P _ _ _ => exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
  | P i a b =>
      cases ξ' with
      | Z => exact absurd h (not_lt_Z' _)
      | P j c d =>
          have hi := hξ.idx; have hj := hξ'.idx; subst hi hj
          cases a with
          | Z =>
              cases c with
              | Z => exact T.Lt.p_tail _ _ _ _ h
              | P _ _ _ => exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
          | P i' a' b' =>
              cases c with
              | Z =>
                  exfalso
                  rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, h', _⟩
                  · omega
                  · exact not_lt_Z' _ h'
                  · cases h'
              | P _ _ _ => exact h

/-! ### Unfolding `phi` -/

/-- Whether `a` is itself a fixed point `ψ₀(B)` of the level above. -/
def pureB (k : Nat) (a : T) : Bool :=
  decide (alphaHead k a ≠ Z) && decide (a = P 0 (alphaHead k a) Z)

/-- The coefficient used when no absorption happens. -/
def coefX (k : Nat) (a ξ : T) : T := if pureB k a then ξ else onePlus ξ

/-- The threshold of `phi k a`. -/
def thrA (k : Nat) (a : T) : T := oadd (OG k a) Om

/-- The fixed-point part of the head argument `d` of `ξ`. -/
def headD (k : Nat) (a d : T) : T := takeW (bigW (thrA k a)) d

/-- `ξ` triggers absorption. -/
def AbsP (k : Nat) (a ξ : T) : Prop := ∃ i d b, ξ = P i d b ∧ alphaHead k a < headD k a d

instance decAbsP (k : Nat) (a : T) : (ξ : T) → Decidable (AbsP k a ξ)
  | Z => isFalse (by rintro ⟨_, _, _, h, _⟩; cases h)
  | P i d b =>
    if h : alphaHead k a < headD k a d then isTrue ⟨i, d, b, rfl, h⟩
    else isFalse (by
      rintro ⟨i', d', b', he, h'⟩
      injection he with _ e2 _
      subst e2
      exact h h')

theorem phi_eq_dflt (k : Nat) (a ξ : T) (h : ¬ AbsP k a ξ) :
    phi k a ξ = P 0 (T.add (alphaHead k a) (OPowTimes k a (coefX k a ξ))) Z := by
  cases ξ with
  | Z => rfl
  | P i d b => exact if_neg (fun h' => h ⟨i, d, b, rfl, h'⟩)

theorem phi_eq_abs (k : Nat) (a : T) {i : Nat} {d b : T} (h : alphaHead k a < headD k a d) :
    phi k a (P i d b) =
      P 0 (T.add (headD k a d) (OPowTimes k a (if d = headD k a d then b else P i d b))) Z :=
  if_pos h

theorem good_coefX {k : Nat} {a ξ : T} (h : Good ξ) : Good (coefX k a ξ) := by
  unfold coefX; split
  · exact h
  · exact good_onePlus h

theorem coefX_ne_Z {k : Nat} {a ξ : T} (h : ξ ≠ Z ∨ pureB k a = false) : coefX k a ξ ≠ Z := by
  unfold coefX; split
  · rename_i hp
    rcases h with h | h
    · exact h
    · rw [hp] at h; cases h
  · exact onePlus_ne_Z ξ

theorem pureB_true {k : Nat} {a : T} (h : pureB k a = true) :
    alphaHead k a ≠ Z ∧ a = P 0 (alphaHead k a) Z := by
  simpa [pureB] using h

theorem allBigK_alphaHead (k : Nat) : ∀ a : T, AllBigK k (alphaHead k a)
  | Z => trivial
  | P j d b => by
      rw [alphaHead_P]
      exact (AllW.allBigK_predA (takeW_all _ d)).mono (Nat.le_succ k)

theorem allBigK_OPowTimes (k : Nat) (a : T) : ∀ {X : T}, Good X → AllBigK k (OPowTimes k a X)
  | Z, _ => trivial
  | P i c b, hX => by
      rw [OPowTimes_P k a i c b (cnt_logA_of_good hX)]
      exact ⟨Or.inr ⟨Nat.le_refl 1, le_tr (copies_le_OGd k a) (le_add_right' _ _)⟩,
        allBigK_OPowTimes k a hX.tail⟩

theorem copies_le_of_oadd {k : Nat} {c : T} (h : copies Om k ≤ oadd Om c) : copies Om k ≤ c := by
  cases k with
  | zero => exact Z_le' _
  | succ k =>
      cases c with
      | Z =>
          exfalso
          rw [oadd_Z_right] at h
          rcases h with h | h
          · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, h', _⟩
            · omega
            · exact not_lt_Z' _ h'
            · cases h'
          · cases h
      | P i x r =>
          rw [show Om = P 1 Z Z from rfl, oadd_P] at h
          split at h
          · exact h
          · exfalso
            rw [oadd_Z_left] at h
            rcases h with h | h
            · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, h', _⟩
              · omega
              · exact not_lt_Z' _ h'
              · cases h'
            · injection h with _ h; cases h

theorem allBigK_of_bigW (k : Nat) {a : T} (ha : Good a) : ∀ {Y : T}, AllW (bigW (thrA k a)) Y →
    AllBigK k Y
  | Z, _ => trivial
  | P i c b, h => by
      refine ⟨?_, allBigK_of_bigW k ha h.2⟩
      rcases bigW_iff.mp h.1 with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h1, copies_le_of_oadd (le_tr ?_ h2)⟩
        unfold thrA
        rw [thr_eq k ha, OG, add_assoc'']
        exact le_add_right' _ _

theorem phi_lvl (k : Nat) (a ξ : T) (ha : Good a) (hξ : Good ξ) : Lvl k (phi k a ξ) := by
  by_cases hA : AbsP k a ξ
  · obtain ⟨i, d, b, rfl, hlt⟩ := hA
    rw [phi_eq_abs k a hlt]
    refine ⟨_, rfl, ?_, ?_⟩
    · intro e
      have := (add_eq_Z_iff.mp e).1
      rw [this] at hlt
      exact not_lt_Z' _ hlt
    · apply AllBigK.add (allBigK_of_bigW k ha (takeW_all _ d))
      apply allBigK_OPowTimes
      split
      · exact hξ.tail
      · exact hξ
  · rw [phi_eq_dflt k a ξ hA]
    refine ⟨_, rfl, ?_, AllBigK.add (allBigK_alphaHead k a) (allBigK_OPowTimes k a (good_coefX hξ))⟩
    intro e
    have he := add_eq_Z_iff.mp e
    cases hp : pureB k a
    · exact coefX_ne_Z (Or.inr hp) (by
        cases hX : coefX k a ξ with
        | Z => rfl
        | P _ _ _ => rw [hX] at he; exact absurd he.2 (by intro e'; cases e'))
    · exact (pureB_true hp).1 he.1

theorem phi_fix_lvl (k : Nat) {Φ : T} (hΦ : Lvl (k + 1) Φ) (_hg : Good Φ) : phi k Φ Z = Φ := by
  obtain ⟨Y, rfl, hY, hb⟩ := hΦ
  rw [phi_eq_dflt k _ Z (by rintro ⟨_, _, _, h, _⟩; cases h)]
  have hB : alphaHead k (P 0 Y Z) = Y := by
    rw [alphaHead_P]; exact takeW_of_all _ _ hb.allW_predA
  have hp : pureB k (P 0 Y Z) = true := by simp [pureB, hB, hY]
  simp only [coefX, hp, if_true, OPowTimes_Z, hB, T.add_Z]

/-! ### Normal forms of the building blocks of `phi` -/

theorem G1_succ_cnt (u : Nat) : ∀ {x : T}, Cnt x → T.G1 (u + 1) x = []
  | Z, _ => rfl
  | P i a b, h => by
      rw [G1_P, if_neg (by rw [h.idx]; omega)]
      exact G1_succ_cnt u h.tail

theorem isNF1_Om : T.isNF1 Om := (isNF1_P_Z_iff 1 Z).mpr ⟨T.isNF1.z, by simp [T.G1]⟩

theorem isNF1_P1_Om : T.isNF1 (P 1 Om Z) := by
  refine (isNF1_P_Z_iff 1 Om).mpr ⟨isNF1_Om, ?_⟩
  intro x hx
  simp [T.G1, Om] at hx
  subst hx
  exact Z_lt_P' _ _ _

theorem isNF1_copies_Om : ∀ k : Nat, T.isNF1 (copies Om k)
  | 0 => T.isNF1.z
  | k + 1 => by
      refine (isNF1_P_iff 1 Om _).mpr ⟨isNF1_P1_Om, isNF1_copies_Om k, ?_⟩
      cases k with
      | zero => exact Z_le' _
      | succ k => exact le_refl' _

theorem isNF1_P1_cnt {x : T} (hx : Good x) : T.isNF1 (P 1 x Z) := by
  refine (isNF1_P_Z_iff 1 x).mpr ⟨hx.nf, ?_⟩
  rw [G1_succ_cnt 0 hx.cnt]
  intro y hy; cases hy

theorem isNF1_omegaTimes : ∀ {a : T}, Good a → T.isNF1 (omegaTimes a)
  | Z, _ => T.isNF1.z
  | P i c b, ha => by
      have hi := ha.idx; subst hi
      show T.isNF1 (P 1 (logA c) (omegaTimes b))
      refine (isNF1_P_iff 1 _ _).mpr ⟨isNF1_P1_cnt (good_logA (isNF1_head ha.nf)),
        isNF1_omegaTimes ha.tail, ?_⟩
      exact (desc_omegaTimes ha).hd

theorem isNF1_OG (k : Nat) {a : T} (ha : Good a) : T.isNF1 (OG k a) := by
  unfold OG
  cases k with
  | zero => exact isNF1_omegaTimes ha
  | succ k =>
      apply isNF1_add (isNF1_copies_Om (k + 1)) (isNF1_omegaTimes ha)
      rw [lastS_copies]
      cases a with
      | Z => exact Z_le' _
      | P j e f =>
          show P 1 (logA e) Z ≤ P 1 Om Z
          have hj := ha.idx; subst hj
          exact Or.inl (T.Lt.p_mid _ _ _ _ _ (Cnt_lt_Om (good_logA (isNF1_head ha.nf)).cnt))

theorem dropOm_suf (x : T) : IsSuf (dropOm x) x := by
  cases x with
  | Z => exact IsSuf.refl _
  | P i a b =>
      by_cases h : i = 1 ∧ a = Z
      · obtain ⟨rfl, rfl⟩ := h
        exact (IsSuf.refl b).tail
      · rw [dropOm_P_ne h]; exact IsSuf.refl _

theorem isNF1_OGd (k : Nat) {a : T} (ha : Good a) : T.isNF1 (OGd k a) := by
  obtain ⟨pre, hpre⟩ := dropOm_suf (OG k a)
  have := isNF1_OG k ha
  rw [hpre] at this
  exact isNF1_of_add_right this

theorem unc_OGd (k : Nat) (a : T) : Unc (OGd k a) := by
  obtain ⟨pre, hpre⟩ := dropOm_suf (OG k a)
  have h := unc_OG k a
  rw [hpre] at h
  clear hpre
  induction pre with
  | Z => exact h
  | P i c b _ ih => rw [add_P] at h; exact ih h.2

theorem G1_one_copies (k : Nat) : ∀ x ∈ T.G1 1 (copies Om k), x = Om ∨ x = Z := by
  induction k with
  | zero => intro x hx; cases hx
  | succ k ih =>
      intro x hx
      show x = Om ∨ x = Z
      have : T.G1 1 (copies Om (k + 1)) = [Om] ++ T.G1 1 Om ++ T.G1 1 (copies Om k) := rfl
      rw [this] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · simp [Om, T.G1] at h; exact Or.inr h
      · exact ih x h

theorem G1_one_omegaTimes : ∀ {a : T}, Good a → ∀ x ∈ T.G1 1 (omegaTimes a), Cnt x
  | Z, _, x, hx => by cases hx
  | P i c b, ha, x, hx => by
      have hi := ha.idx; subst hi
      have hl := good_logA (isNF1_head ha.nf)
      have : T.G1 1 (omegaTimes (P 0 c b)) = [logA c] ++ T.G1 1 (logA c) ++
          T.G1 1 (omegaTimes b) := rfl
      rw [this, G1_succ_cnt 0 hl.cnt] at hx
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with h | h
      · rw [h]; exact hl.cnt
      · exact G1_one_omegaTimes ha.tail x h

theorem G1_sub_of_suf {u : Nat} {y x : T} (h : IsSuf y x) : ∀ z ∈ T.G1 u y, z ∈ T.G1 u x := by
  obtain ⟨pre, rfl⟩ := h
  intro z hz
  rw [G1_add]
  exact List.mem_append_right _ hz

theorem G1_one_OGd (k : Nat) {a : T} (ha : Good a) :
    ∀ x ∈ T.G1 1 (OGd k a), Cnt x ∨ (1 ≤ k ∧ x = Om) := by
  intro x hx
  have hx' := G1_sub_of_suf (dropOm_suf (OG k a)) x hx
  unfold OG at hx'
  rw [G1_add, List.mem_append] at hx'
  rcases hx' with h | h
  · rcases G1_one_copies k x h with h' | h'
    · right
      refine ⟨?_, h'⟩
      cases k with
      | zero => cases h
      | succ k => omega
    · left; rw [h']; trivial
  · exact Or.inl (G1_one_omegaTimes ha x h)

theorem OGd_head (k : Nat) (a : T) : 1 ≤ k → ∃ r, OGd k a = P 1 Om r := by
  intro hk
  cases k with
  | zero => exfalso; omega
  | succ k =>
      unfold OGd OG
      rw [show copies Om (k + 1) = P 1 Om (copies Om k) from rfl, add_P,
        dropOm_P_ne (by intro h; cases h.2)]
      exact ⟨_, rfl⟩

theorem isNF1_OPT_summand (k : Nat) {a c : T} (ha : Good a) (hc : Good (logA c)) :
    T.isNF1 (P 1 (T.add (OGd k a) (logA c)) Z) := by
  refine (isNF1_P_Z_iff 1 _).mpr ⟨?_, ?_⟩
  · by_cases h0 : OGd k a = Z
    · rw [h0]; exact hc.nf
    · apply isNF1_add (isNF1_OGd k ha) hc.nf
      exact head_cnt_le_lastS (unc_OGd k a) h0 hc.cnt
  · intro x hx
    rw [G1_add, G1_succ_cnt 0 hc.cnt, List.append_nil] at hx
    have h0 : OGd k a ≠ Z := by intro e; rw [e] at hx; cases hx
    rcases G1_one_OGd k ha x hx with hcx | ⟨hk1, rfl⟩
    · exact lt_unc_add (unc_OGd k a) h0 _ (cnt_head_of_cnt hcx)
    · obtain ⟨r, hr⟩ := OGd_head k a hk1
      rw [hr, add_P]
      exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)

theorem isNF1_OPowTimes (k : Nat) {a : T} (ha : Good a) : ∀ {X : T}, Good X →
    T.isNF1 (OPowTimes k a X)
  | Z, _ => T.isNF1.z
  | P i c b, hX => by
      rw [OPowTimes_P k a i c b (cnt_logA_of_good hX)]
      have hi := hX.idx; subst hi
      refine (isNF1_P_iff 1 _ _).mpr ⟨isNF1_OPT_summand k ha (good_logA (isNF1_head hX.nf)),
        isNF1_OPowTimes k ha hX.tail, ?_⟩
      cases b with
      | Z => exact Z_le' _
      | P j c' b' =>
          rw [OPowTimes_P k a j c' b' (cnt_logA_of_good hX.tail)]
          show P 1 (T.add (OGd k a) (logA c')) Z ≤ P 1 (T.add (OGd k a) (logA c)) Z
          have hj := hX.tail.idx; subst hj
          rcases logA_le_logA (isNF1_head hX.tail.nf) (isNF1_head hX.nf)
              (P0_le_P0_iff.mp hX.desc.hd) with h | h
          · exact Or.inl (T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr h))
          · rw [h]; exact le_refl' _

theorem AllW.lastS' {p : Nat → T → Bool} : ∀ {X : T}, AllW p X → X ≠ Z →
    ∃ i c, lastS X = P i c Z ∧ p i c = true
  | Z, _, h => absurd rfl h
  | P i c Z, h, _ => ⟨i, c, rfl, h.1⟩
  | P i c (P j e f), h, _ => by rw [lastS_P_P]; exact AllW.lastS' h.2 nofun

/-- The head of `O` lies below the threshold. -/
def HeadBelow (thr O : T) : Prop := ∀ i e r, O = P i e r → i = 0 ∨ (i = 1 ∧ oadd Om e < thr)

theorem headBelow_of_not_big {thr : T} {i : Nat} {c r : T} (h : bigW thr i c = false) :
    HeadBelow thr (P i c r) := by
  intro i' e r' he
  injection he with h1 h2 _
  subst h1 h2
  have h' : ¬ (2 ≤ i ∨ (1 ≤ i ∧ thr ≤ oadd Om c)) := by rw [← bigW_iff, h]; simp
  have hi : i ≤ 1 := by omega
  rcases Nat.lt_or_ge i 1 with h1 | h1
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rcases lt_total_thm (oadd Om c) thr with h2 | h2 | h2
    · exact h2
    · exact absurd (Or.inr ⟨h1, Or.inl h2⟩) h'
    · exact absurd (Or.inr ⟨h1, Or.inr h2.symm⟩) h'

theorem lt_of_headBelow {thr O : T} {i : Nat} {c r : T} (hO : HeadBelow thr O)
    (hb : bigW thr i c = true) : O < P i c r := by
  cases O with
  | Z => exact Z_lt_P' _ _ _
  | P j e b =>
      apply P_lt_P_of_head_lt
      rcases hO j e b rfl with h | ⟨rfl, h⟩
      · subst h
        rcases bigW_iff.mp hb with h' | ⟨h', _⟩
        · exact T.Lt.p_head _ _ _ _ _ _ (by omega)
        · exact T.Lt.p_head _ _ _ _ _ _ (by omega)
      · exact lt_big hb h

theorem pre_lt' {thr : T} : ∀ {Pre D O : T} (W : T), Pre < D →
    (∀ r, D = T.add Pre r → AllW (bigW thr) r) → HeadBelow thr O → T.add Pre O < T.add D W
  | Z, Z, _, _, hlt, _, _ => absurd hlt (lt_irr _)
  | Z, P i c r, O, W, _, hD, hO => by
      rw [add_Z_left', add_P]
      exact lt_of_headBelow hO (hD (P i c r) rfl).1
  | P _ _ _, Z, _, _, hlt, _, _ => absurd hlt (not_lt_Z' _)
  | P i a b, P j c d, O, W, hlt, hD, hO => by
      rw [add_P, add_P]
      rcases lt_inv _ _ _ _ _ _ hlt with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
      · exact T.Lt.p_head _ _ _ _ _ _ h'
      · exact T.Lt.p_mid _ _ _ _ _ h'
      · apply T.Lt.p_tail
        exact pre_lt' W h' (fun r hr => hD r (by rw [add_P, hr])) hO

/-- A chain whose head is below the exponent level `G` is below any chain of exponent `≥ G`. -/
theorem lt_of_head_exp {G O e r : T} (hO : HeadBelow G O) (he : G ≤ oadd Om e) : O < P 1 e r := by
  cases O with
  | Z => exact Z_lt_P' _ _ _
  | P j c b =>
      apply P_lt_P_of_head_lt
      rcases hO j c b rfl with h | ⟨rfl, h⟩
      · subst h; exact T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one
      · exact T.Lt.p_mid _ _ _ _ _ (lt_of_oadd_Om_lt (lt_of_lt_of_le' h he))

/-! ### The Buchholz bound for components -/

theorem isNF1_of_G1 {u : Nat} : ∀ {x : T}, T.isNF1 x → ∀ y ∈ T.G1 u x, T.isNF1 y
  | Z, _, _, hy => absurd hy List.not_mem_nil
  | P i a b, hx, y, hy => by
      rw [G1_P] at hy
      split at hy
      · simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with (rfl | hy) | hy
        · exact isNF1_arg hx
        · exact isNF1_of_G1 (isNF1_arg hx) y hy
        · exact isNF1_of_G1 (isNF1_tail hx) y hy
      · exact isNF1_of_G1 (isNF1_tail hx) y hy

theorem uncPart_add_unc : ∀ {Pre : T}, Unc Pre → ∀ X : T, uncPart (T.add Pre X) = T.add Pre (uncPart X)
  | Z, _, _ => rfl
  | P 0 _ _, h, _ => absurd h.1 (by omega)
  | P (i + 1) a b, h, X => by
      rw [add_P, add_P]
      show P (i + 1) a (uncPart (T.add b X)) = _
      rw [uncPart_add_unc h.2 X]

theorem mem_G1_unc {h Pre c rest : T} {i : Nat} (hPre : Unc Pre) (hi : 1 ≤ i)
    (hh : h = T.add Pre (P i c rest)) : c ∈ T.G1 0 (uncPart h) := by
  rw [hh, uncPart_add_unc hPre, G1_add]
  apply List.mem_append_right
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  show c ∈ T.G1 0 (P (j + 1) c (uncPart rest))
  rw [G1_P0]; simp

theorem Z_lt_logA {h : T} (hU : uncPart h ≠ Z) : Z < logA h :=
  lt_of_head_lt (lt_of_lt_of_le' (Z_lt_P' 0 _ Z) (head_le_logA hU))

theorem cnt_comp_lt_logA {h x : T} (hh : T.isNF1 (P 0 h Z)) (hU : uncPart h ≠ Z)
    (hx : x ∈ T.G1 0 (uncPart h)) (hcx : Cnt x) : x < logA h := by
  apply lt_of_head_lt
  refine lt_of_lt_of_le' ?_ (head_le_logA hU)
  exact head_lt_of_lt_single (lt_psi_of_comp (isNF1_psi_unc hh) x hx hcx)

theorem tail_lt_logA {h c G lam : T} (hh : T.isNF1 (P 0 h Z)) (hU : uncPart h ≠ Z)
    (hc : c ∈ T.G1 0 (uncPart h)) (hG : c = T.add G lam) (hlam : Cnt lam) : lam < logA h := by
  cases lam with
  | Z => exact Z_lt_logA hU
  | P i l lr =>
      have hi := hlam.idx; subst hi
      have hl : l ∈ T.G1 0 (uncPart h) := G1_trans 0 hc l (by rw [hG, G1_add, G1_P0]; simp)
      apply lt_of_head_lt
      refine lt_of_lt_of_le' ?_ (head_le_logA hU)
      exact T.Lt.p_mid _ _ _ _ _ (isNF1_G (isNF1_psi_unc hh) l hl)

theorem oadd_Om_arg {c G σ c3 : T} (h : oadd Om c = T.add G (P 1 σ c3)) :
    σ ∈ T.G1 0 c ∨ σ = Z := by
  rw [show Om = P 1 Z Z from rfl, oadd_P] at h
  split at h
  · left; rw [h, G1_add, G1_P0]; simp
  · rw [oadd_Z_left] at h
    cases G with
    | Z => injection h with _ h2 _; exact Or.inr h2.symm
    | P i x G' =>
        rw [add_P] at h
        injection h with _ _ h3
        left; rw [h3, G1_add, G1_P0]; simp

theorem oadd_Om_suffix {c G lam : T} (hG : G ≠ Z) (h : oadd Om c = T.add G lam) :
    ∃ G', c = T.add G' lam := by
  rw [show Om = P 1 Z Z from rfl, oadd_P] at h
  split at h
  · exact ⟨G, h⟩
  · rw [oadd_Z_left] at h
    cases G with
    | Z => exact absurd rfl hG
    | P i x G' =>
        rw [add_P] at h
        injection h with _ _ h3
        exact ⟨G', h3⟩

theorem not_le_iff_lt {x y : T} (h : ¬ x ≤ y) : y < x := by
  rcases lt_total_thm x y with h' | h' | h'
  · exact absurd (Or.inl h') h
  · exact h'
  · exact absurd (Or.inr h') h

theorem oadd_Om_lt_copies {k : Nat} {c : T} (hc : c < copies Om (k + 1)) :
    oadd Om c < copies Om (k + 1) := by
  rw [show Om = P 1 Z Z from rfl, oadd_P]
  split
  · exact hc
  · show P 1 Z (oadd Z c) < P 1 Om (copies Om k)
    exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)

/-- **K1**: summands of `uncPart` of the head argument of `a` failing `predA` lie below `OG`. -/
theorem K1core (k : Nat) {da ra c rest Pre : T} (ha : Good (P 0 da ra)) (hPre : Unc Pre)
    (hh : da = T.add Pre (P 1 c rest)) (hnot : predA k 1 c = false) :
    oadd Om c < OG k (P 0 da ra) := by
  have hhn := isNF1_head ha.nf
  have hcmem := mem_G1_unc hPre (Nat.le_refl 1) hh
  have hU : uncPart da ≠ Z := by intro e; rw [e] at hcmem; cases hcmem
  have hc : c < copies Om (k + 1) := by
    apply not_le_iff_lt
    intro h'
    have := predA_iff.mpr (Or.inr ⟨Nat.le_refl 1, h'⟩ : BigK (k + 1) 1 c)
    rw [hnot] at this; cases this
  have hoc := oadd_Om_lt_copies hc
  unfold OG
  by_cases hlt : oadd Om c < copies Om k
  · exact lt_of_lt_of_le' hlt (le_add_right' _ _)
  · have hle : copies Om k ≤ oadd Om c := le_of_not_lt' hlt
    rw [copies_add Om k 1] at hoc
    obtain ⟨c'', hc''⟩ := between_prefix hle hoc
    rw [hc''] at hoc ⊢
    have hc''lt : c'' < P 1 Om Z := (add_lt_add_left_iff _).mp hoc
    apply (add_lt_add_left_iff _).mpr
    show c'' < P 1 (logA da) (omegaTimes ra)
    cases c'' with
    | Z => exact Z_lt_P' _ _ _
    | P j σ c3 =>
        rcases lt_inv _ _ _ _ _ _ hc''lt with h' | ⟨rfl, h'⟩ | ⟨rfl, _, h'⟩
        · exact T.Lt.p_head _ _ _ _ _ _ h'
        · apply P_lt_P_of_head_lt
          apply T.Lt.p_mid
          rcases oadd_Om_arg hc'' with hσ | hσ
          · have hσmem : σ ∈ T.G1 0 (uncPart da) := G1_trans 0 hcmem σ hσ
            have hσnf : T.isNF1 σ := isNF1_of_G1 (isNF1_arg (isNF1_psi_unc hhn)) σ hσmem
            exact cnt_comp_lt_logA hhn hU hσmem
              (Cnt_of_lt_Om (isNF1_desc hσnf) h')
          · rw [hσ]; exact Z_lt_logA hU
        · exact absurd h' (not_lt_Z' _)

/-- **K2/K3**: non-big summands of `uncPart h` lie below the first summand of `OPowTimes`. -/
theorem NBcore (k : Nat) {a h c rest Pre : T} (ha : Good a) (hk : k = 0 → a ≠ Z)
    (hh : T.isNF1 (P 0 h Z)) (hPre : Unc Pre) (hhe : h = T.add Pre (P 1 c rest))
    (hnot : bigW (thrA k a) 1 c = false) : c < T.add (OGd k a) (logA h) := by
  have hcmem := mem_G1_unc hPre (Nat.le_refl 1) hhe
  have hU : uncPart h ≠ Z := by intro e; rw [e] at hcmem; cases hcmem
  have hl := good_logA hh
  have hOG := OG_ne_Z hk
  apply lt_of_oadd_Om_lt
  rw [exp_OGd ha hOG hl.cnt]
  have hlt : oadd Om c < T.add (OG k a) Om := by
    have h1 := headBelow_of_not_big (r := Z) hnot 1 c Z rfl
    rcases h1 with h1 | ⟨_, h1⟩
    · exfalso; omega
    · unfold thrA at h1; rwa [thr_eq k ha] at h1
  by_cases h2 : oadd Om c < OG k a
  · exact lt_of_lt_of_le' h2 (le_add_right' _ _)
  · obtain ⟨lam, hlam⟩ := between_prefix (le_of_not_lt' h2) hlt
    rw [hlam] at hlt ⊢
    have hlamOm : lam < Om := (add_lt_add_left_iff _).mp hlt
    have hcnf : T.isNF1 c := isNF1_of_G1 (isNF1_arg (isNF1_psi_unc hh)) c hcmem
    have hdesc : Desc (oadd Om c) := oadd_desc (Desc.single 1 Z) (isNF1_desc hcnf)
    rw [hlam] at hdesc
    have hdl : Desc lam := by
      clear hlam hlt
      generalize OG k a = G at hdesc
      induction G with
      | Z => exact hdesc
      | P i x r _ ih => rw [add_P] at hdesc; exact ih hdesc.tail
    have hcl : Cnt lam := Cnt_of_lt_Om hdl hlamOm
    obtain ⟨G', hG'⟩ := oadd_Om_suffix hOG hlam
    exact (add_lt_add_left_iff _).mpr (tail_lt_logA hh hU hcmem hG' hcl)

/-! ### Components of `OPowTimes` -/

theorem G1_oadd_sub {u : Nat} : ∀ {p q : T}, ∀ x ∈ T.G1 u (oadd p q), x ∈ T.G1 u p ∨ x ∈ T.G1 u q
  | Z, _, x, hx => Or.inr hx
  | P i a b, q, x, hx => by
      rw [oadd_P] at hx
      split at hx
      · exact Or.inr hx
      · rw [G1_P] at hx
        rw [G1_P]
        split at hx
        · rename_i hu
          rw [if_pos hu]
          simp only [List.mem_append, List.mem_singleton] at hx ⊢
          rcases hx with (h | h) | h
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inl (Or.inl (Or.inr h))
          · rcases G1_oadd_sub x h with h' | h'
            · exact Or.inl (Or.inr h')
            · exact Or.inr h'
        · rename_i hu
          rw [if_neg hu]
          exact G1_oadd_sub x hx

theorem uncPart_le (c : T) : uncPart c ≤ c := by
  conv => rhs; rw [← uncPart_add_cntPart c]
  exact le_add_right' _ _

theorem G1_logA_sub {c : T} : ∀ x ∈ T.G1 0 (logA c), x ∈ T.G1 0 c ∨ x = uncPart c := by
  intro x hx
  by_cases hU : uncPart c = Z
  · rw [logA_of_unc_Z hU] at hx; exact Or.inl hx
  · rw [logA_of_unc_ne hU] at hx
    have hcU := uncPart_add_cntPart c
    rcases G1_oadd_sub x hx with h | h
    · rw [G1_P0, G1_Z, List.append_nil, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inr h
      · left; rw [← hcU, G1_add]; exact List.mem_append_left _ h
    · left; rw [← hcU, G1_add]; exact List.mem_append_right _ h

/-- Components of `log c` for a summand argument `c` bounded by `D`. -/
theorem logA_comp_le {X D c : T} (hcX : c ∈ T.G1 0 X) (hXD : ∀ y ∈ T.G1 0 X, y ≤ D) :
    ∀ x ∈ T.G1 0 (logA c), x ≤ D := by
  intro x hx
  rcases G1_logA_sub x hx with h | h
  · exact hXD x (G1_trans 0 hcX x h)
  · rw [h]; exact le_tr (uncPart_le c) (hXD c hcX)

theorem omegaTimes_comps : ∀ {a : T}, Good a → ∀ {D : T}, (∀ y ∈ T.G1 0 a, y ≤ D) →
    ∀ x ∈ T.G1 0 (omegaTimes a), Cnt x ∨ x ≤ D
  | Z, _, _, _, x, hx => by cases hx
  | P i c b, ha, D, hD, x, hx => by
      have hi := ha.idx; subst hi
      have : T.G1 0 (omegaTimes (P 0 c b)) =
          [logA c] ++ T.G1 0 (logA c) ++ T.G1 0 (omegaTimes b) := rfl
      rw [this] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | h
      · left; rw [h]; exact (good_logA (isNF1_head ha.nf)).cnt
      · right; exact logA_comp_le (by rw [G1_P0]; simp) hD x h
      · exact omegaTimes_comps ha.tail (fun y hy => hD y (by rw [G1_P0]; simp [hy])) x h

theorem copies_comps : ∀ (k : Nat), ∀ x ∈ T.G1 0 (copies Om k), x = Om ∨ x = Z
  | 0, x, hx => by cases hx
  | k + 1, x, hx => by
      have : T.G1 0 (copies Om (k + 1)) = [Om] ++ T.G1 0 Om ++ T.G1 0 (copies Om k) := rfl
      rw [this] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · simp [Om, T.G1] at h; exact Or.inr h
      · exact copies_comps k x h

theorem OGd_comps (k : Nat) {a : T} (ha : Good a) {D : T} (hD : ∀ y ∈ T.G1 0 a, y ≤ D) :
    ∀ x ∈ T.G1 0 (OGd k a), (1 ≤ k ∧ x = Om) ∨ x = Z ∨ Cnt x ∨ x ≤ D := by
  intro x hx
  have hx' := G1_sub_of_suf (dropOm_suf (OG k a)) x hx
  unfold OG at hx'
  rw [G1_add, List.mem_append] at hx'
  rcases hx' with h | h
  · rcases copies_comps k x h with h' | h'
    · left
      refine ⟨?_, h'⟩
      cases k with
      | zero => cases h
      | succ k => omega
    · exact Or.inr (Or.inl h')
  · rcases omegaTimes_comps ha hD x h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

theorem arg_lt_self {i : Nat} {e : T} (he : T.isNF1 (P i e Z)) (hidx : ∀ j x r, e = P j x r → j ≤ i) :
    e < P i e Z := by
  cases e with
  | Z => exact Z_lt_P' _ _ _
  | P j x r =>
      rcases Nat.lt_or_ge j i with h | h
      · exact T.Lt.p_head _ _ _ _ _ _ h
      · have hj : j = i := Nat.le_antisymm (hidx j x r rfl) h
        subst hj
        apply T.Lt.p_mid
        apply isNF1_G he x
        rw [G1_P, if_pos (Nat.le_refl _)]; simp

theorem IsSuf.tail' {i : Nat} {a b x : T} (h : IsSuf (P i a b) x) : IsSuf b x := by
  obtain ⟨pre, rfl⟩ := h
  exact ⟨T.add pre (P i a T.Z), by rw [add_assoc'', add_P, add_Z_left']⟩

/-- All summands have index exactly `1`. -/
def Idx1 : T → Prop
  | Z => True
  | P i _ b => i = 1 ∧ Idx1 b

theorem Idx1.add : ∀ {X Y : T}, Idx1 X → Idx1 Y → Idx1 (T.add X Y)
  | Z, _, _, hY => hY
  | P _ _ _, _, hX, hY => by rw [add_P]; exact ⟨hX.1, Idx1.add hX.2 hY⟩

theorem idx1_copies (x : T) : ∀ k : Nat, Idx1 (copies x k)
  | 0 => trivial
  | k + 1 => ⟨rfl, idx1_copies x k⟩

theorem idx1_omegaTimes : ∀ x : T, Idx1 (omegaTimes x)
  | Z => trivial
  | P _ _ b => ⟨rfl, idx1_omegaTimes b⟩

theorem idx1_OGd (k : Nat) (a : T) : Idx1 (OGd k a) := by
  obtain ⟨pre, hpre⟩ := dropOm_suf (OG k a)
  have h : Idx1 (OG k a) := Idx1.add (idx1_copies Om k) (idx1_omegaTimes a)
  rw [hpre] at h
  clear hpre
  induction pre with
  | Z => exact h
  | P i c b _ ih => rw [add_P] at h; exact ih h.2

theorem OPT_arg_idx (k : Nat) (a c : T) (hc : Cnt (logA c)) :
    ∀ j x r, T.add (OGd k a) (logA c) = P j x r → j ≤ 1 := by
  intro j x r h
  have hi := idx1_OGd k a
  cases hO : OGd k a with
  | Z =>
      rw [hO] at h
      rw [show T.add Z (logA c) = logA c from rfl] at h
      rw [h] at hc; rw [hc.idx]; omega
  | P i y s =>
      rw [hO, add_P] at h
      injection h with h1 _ _
      rw [hO] at hi
      have := hi.1
      omega

theorem comps_lt (k : Nat) {a DX rX Y : T} (ha : Good a) (hk : k = 0 → a ≠ Z)
    (hX : Good (P 0 DX rX)) (hY1 : P 1 (T.add (OGd k a) (logA DX)) Z ≤ Y)
    (hYa : ∀ da ra, a = P 0 da ra → da < Y) (hYX : DX < Y) :
    ∀ x ∈ T.G1 0 (OPowTimes k a (P 0 DX rX)), x < Y := by
  have hDXn := isNF1_head hX.nf
  have hl1 := good_logA hDXn
  have hnf1 := isNF1_OPT_summand k ha hl1
  have he1 := arg_lt_self hnf1 (OPT_arg_idx k a DX hl1.cnt)
  have hP1Y : T.add (OGd k a) (logA DX) < Y := lt_of_lt_of_le' he1 hY1
  have hOmY : Om ≤ Y := by
    refine le_tr ?_ hY1
    cases hE : T.add (OGd k a) (logA DX) with
    | Z => exact le_refl' _
    | P _ _ _ => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _))
  have hZY : Z < Y := lt_of_lt_of_le' (Z_lt_P' _ _ _) hOmY
  obtain ⟨D, hDa, hDY⟩ : ∃ D, (∀ y ∈ T.G1 0 a, y ≤ D) ∧ D < Y := by
    cases a with
    | Z => exact ⟨Z, fun y hy => absurd hy List.not_mem_nil, hZY⟩
    | P i da ra =>
        have hi := ha.idx; subst hi
        exact ⟨da, comps_le_head_arg ha.nf, hYa da ra rfl⟩
  have hXD := comps_le_head_arg hX.nf
  suffices H : ∀ X', IsSuf X' (P 0 DX rX) → ∀ x ∈ T.G1 0 (OPowTimes k a X'), x < Y from
    H _ (IsSuf.refl _)
  intro X'
  induction X' with
  | Z => intro _ x hx; cases hx
  | P j c b' _ ih =>
      intro hsuf x hx
      have hX' : Good (P j c b') := hsuf.good hX
      have hj := hX'.idx; subst hj
      have hcX : c ∈ T.G1 0 (P 0 DX rX) :=
        G1_sub_of_suf hsuf c (by rw [G1_P0]; simp)
      rw [OPowTimes_P k a 0 c b' (cnt_logA_of_good hX'), G1_P,
        if_pos (Nat.zero_le 1)] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | h) | h
      · rw [h]
        refine lt_of_le_of_lt' ?_ hP1Y
        apply (add_le_add_left_iff _).mpr
        exact logA_le_logA (isNF1_head hX'.nf) hDXn (hXD c hcX)
      · rw [G1_add, List.mem_append] at h
        rcases h with h | h
        · rcases OGd_comps k ha hDa x h with ⟨hk1, rfl⟩ | rfl | hcx | hle
          · refine lt_of_lt_of_le' ?_ hY1
            apply T.Lt.p_mid
            obtain ⟨r, hr⟩ := OGd_head k a hk1
            rw [hr, add_P]; exact Z_lt_P' _ _ _
          · exact hZY
          · exact lt_of_lt_of_le' (Cnt_lt_Om hcx) hOmY
          · exact lt_of_le_of_lt' hle hDY
        · exact lt_of_le_of_lt' (logA_comp_le hcX hXD x h) hYX
      · exact ih (IsSuf.tail' hsuf) x h

theorem nf_main (k : Nat) {a Pre h X : T} (ha : Good a) (hk : k = 0 → a ≠ Z) (hX : Good X)
    (hh : T.isNF1 (P 0 h Z)) (hPre : ∃ rest, h = T.add Pre rest)
    (hall : AllW (bigW (thrA k a)) Pre)
    (hcomp : ∀ x ∈ T.G1 0 (OPowTimes k a X), x < T.add Pre (OPowTimes k a X)) :
    T.isNF1 (P 0 (T.add Pre (OPowTimes k a X)) Z) := by
  obtain ⟨rest, hrest⟩ := hPre
  have hhn := isNF1_arg hh
  have hPren : T.isNF1 Pre := by rw [hrest] at hhn; exact isNF1_of_add_left hhn
  have hOn := isNF1_OPowTimes k ha hX
  refine (isNF1_P_Z_iff 0 _).mpr ⟨?_, ?_⟩
  · by_cases hP0 : Pre = Z
    · rw [hP0]; exact hOn
    · apply isNF1_add hPren hOn
      obtain ⟨i, c, hl, hb⟩ := hall.lastS' hP0
      rw [hl]
      have hexp := expBelow_OPowTimes k ha hk hX
      cases hO : OPowTimes k a X with
      | Z => exact Z_le' _
      | P j e r =>
          rw [hO] at hexp
          obtain ⟨rfl, he, -⟩ := hexp
          exact Or.inl (lt_big hb he)
  · intro x hx
    rw [G1_add, List.mem_append] at hx
    rcases hx with hx | hx
    · have hxh : x ∈ T.G1 0 h := by rw [hrest, G1_add]; exact List.mem_append_left _ hx
      have := isNF1_G hh x hxh
      rw [hrest] at this
      exact lt_of_lt_of_le' (lt_prefix_of_comp hx this) (le_add_right' _ _)
    · exact hcomp x hx

theorem head_le_Y (k : Nat) {a Pre DX rX : T} (ha : Good a) (hk : k = 0 → a ≠ Z)
    (hX : Good (P 0 DX rX)) (hall : AllW (bigW (thrA k a)) Pre) :
    P 1 (T.add (OGd k a) (logA DX)) Z ≤ T.add Pre (OPowTimes k a (P 0 DX rX)) := by
  have hexp := expBelow_OPowTimes k ha hk hX
  rw [OPowTimes_P k a 0 DX rX (cnt_logA_of_good hX)] at hexp ⊢
  cases Pre with
  | Z => exact P_le_P_tail (Z_le' _)
  | P i c P' =>
      rw [add_P]
      exact Or.inl (P_lt_P_of_head_lt _ _ (lt_big hall.1 hexp.2.1))

theorem AllW.unc_predA {k : Nat} : ∀ {X : T}, AllW (predA k) X → Unc X
  | Z, _ => trivial
  | P i c b, h => ⟨by rcases predA_iff.mp h.1 with h' | ⟨h', _⟩ <;> omega, AllW.unc_predA h.2⟩

theorem AllW.unc_bigW {thr : T} : ∀ {X : T}, AllW (bigW thr) X → Unc X
  | Z, _ => trivial
  | P i c b, h => ⟨by rcases bigW_iff.mp h.1 with h' | ⟨h', _⟩ <;> omega, AllW.unc_bigW h.2⟩

/-- The rest of the head argument of `a` after its level-`k+1` part lies below `OG`. -/
theorem headBelow_restA (k : Nat) {da ra : T} (ha : Good (P 0 da ra)) :
    HeadBelow (OG k (P 0 da ra)) (dropW (predA k) da) := by
  intro i c rr he
  have hdec : da = T.add (takeW (predA k) da) (P i c rr) := by
    rw [← he, takeW_add_dropW]
  rcases dropW_head (predA k) da with h0 | ⟨i', c', rr', h1, h2⟩
  · rw [h0] at he; cases he
  · have heq : P i' c' rr' = P i c rr := h1.symm.trans he
    injection heq with e1 e2 _
    rw [e1, e2] at h2
    rcases Nat.lt_or_ge i 1 with hi | hi
    · left; omega
    · have hi1 : i = 1 := by
        rcases Nat.lt_or_ge i 2 with hi2 | hi2
        · omega
        · exfalso
          have : predA k i c = true := predA_iff.mpr (Or.inl hi2)
          rw [h2] at this; cases this
      subst hi1
      right
      exact ⟨rfl, K1core k ha (AllW.unc_predA (takeW_all _ da)) hdec h2⟩

theorem HeadBelow.mono {G G' O : T} (h : HeadBelow G O) (hG : G ≤ G') : HeadBelow G' O := by
  intro i e r he
  rcases h i e r he with h' | ⟨h1, h2⟩
  · exact Or.inl h'
  · exact Or.inr ⟨h1, lt_of_lt_of_le' h2 hG⟩

theorem OG_le_thrA (k : Nat) {a : T} (ha : Good a) : OG k a ≤ thrA k a := by
  unfold thrA; rw [thr_eq k ha]; exact le_add_right' _ _

/-- **K1** in both shapes. -/
theorem K1_lt (k : Nat) {da ra Pre O W : T} (ha : Good (P 0 da ra)) (hk : k = 0 → P 0 da ra ≠ Z)
    (hcase : (Pre = alphaHead k (P 0 da ra) ∧ (O ≠ Z) ∧
        (∀ j e r, O = P j e r → j = 1 ∧ OG k (P 0 da ra) ≤ oadd Om e)) ∨
      (alphaHead k (P 0 da ra) < Pre ∧
        ∀ r, Pre = T.add (alphaHead k (P 0 da ra)) r → AllW (bigW (thrA k (P 0 da ra))) r)) :
    da < T.add Pre (T.add O W) := by
  have hdec := takeW_add_dropW (predA k) da
  have hHB := headBelow_restA k ha
  rcases hcase with ⟨rfl, hO0, hOexp⟩ | ⟨hlt, hD⟩
  · rw [alphaHead_P]
    conv => lhs; rw [← hdec]
    apply (add_lt_add_left_iff _).mpr
    cases hO : O with
    | Z => exact absurd hO hO0
    | P j e r =>
        rw [add_P]
        obtain ⟨rfl, hle⟩ := hOexp j e r hO
        exact lt_of_head_exp hHB hle
  · conv => lhs; rw [← hdec]
    rw [alphaHead_P] at hlt hD
    exact pre_lt' (thr := thrA k (P 0 da ra)) _ hlt hD (hHB.mono (OG_le_thrA k ha))

/-- **K2/K3**: the head argument of `ξ` lies below `Pre ++ OPowTimes ξ` when `Pre` is its
fixed-point part. -/
theorem nb_lt (k : Nat) {a h b Pre : T} (ha : Good a) (hk : k = 0 → a ≠ Z) (hh : Good (P 0 h b))
    (hPre : Unc Pre) (hd : h = T.add Pre (dropW (bigW (thrA k a)) h)) :
    h < T.add Pre (OPowTimes k a (P 0 h b)) := by
  rw [OPowTimes_P k a 0 h b (cnt_logA_of_good hh)]
  conv => lhs; rw [hd]
  apply (add_lt_add_left_iff _).mpr
  rcases dropW_head (bigW (thrA k a)) h with h0 | ⟨i, c, rr, h1, h2⟩
  · rw [h0]; exact Z_lt_P' _ _ _
  · rw [h1]
    rcases headBelow_of_not_big (r := rr) h2 i c rr rfl with hi | ⟨rfl, _⟩
    · subst hi; exact T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one
    · apply T.Lt.p_mid
      rw [h1] at hd
      exact NBcore k ha hk (isNF1_head hh.nf) hPre hd h2

/-! ### Monotonicity and fixed points of `phi` -/

theorem AllW.add {p : Nat → T → Bool} : ∀ {X Y : T}, AllW p X → AllW p Y → AllW p (T.add X Y)
  | Z, _, _, hY => hY
  | P _ _ _, _, hX, hY => by rw [add_P]; exact ⟨hX.1, AllW.add hX.2 hY⟩

theorem AllW.imp {p q : Nat → T → Bool} (hpq : ∀ i c, p i c = true → q i c = true) :
    ∀ {X : T}, AllW p X → AllW q X
  | Z, _ => trivial
  | P i c _, h => ⟨hpq i c h.1, AllW.imp hpq h.2⟩

theorem alphaHead_le (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (h : α ≤ β) :
    alphaHead k α ≤ alphaHead k β := by
  cases α with
  | Z => exact Z_le' _
  | P i d b =>
      cases β with
      | Z =>
          rcases h with h | h
          · exact absurd h (not_lt_Z' _)
          · cases h
      | P j d' b' =>
          rw [alphaHead_P, alphaHead_P]
          apply takeW_le_takeW (upW_predA k)
          have hi := hα.idx; have hj := hβ.idx; subst hi hj
          rcases h with h | h
          · exact P0_le_P0_iff.mp (head_le_of_P_lt h)
          · injection h with _ h; exact Or.inr h

theorem oadd_Om_of_ge {k : Nat} {c : T} (h : copies Om (k + 1) ≤ c) : oadd Om c = c := by
  cases c with
  | Z =>
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i x r =>
      rw [show Om = P 1 Z Z from rfl]
      apply oadd_P_of_lt
      show P 1 Z Z < P i x Z
      have h' : P 1 Om Z ≤ P i x Z := by
        rcases h with h | h
        · exact head_le_of_P_lt h
        · injection h with h1 h2; subst h1 h2; exact le_refl' _
      exact lt_of_lt_of_le' (T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)) h'

theorem predA_to_bigW (k : Nat) {α : T} (hα : Good α) {i : Nat} {c : T} (h : predA k i c = true) :
    bigW (thrA k α) i c = true := by
  rw [predA_iff] at h
  rw [bigW_iff]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    rw [oadd_Om_of_ge h2]
    exact le_tr (Or.inl (thr_lt_copies k hα)) h2

theorem thrA_le (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (h : α < β) :
    thrA k α ≤ thrA k β := by
  unfold thrA
  rw [thr_eq k hα, thr_eq k hβ]
  exact le_tr (OG_succ_le k hα hβ h) (le_add_right' _ _)

theorem bigW_of_le {thr thr' : T} (h : thr ≤ thr') {i : Nat} {c : T} (hb : bigW thr' i c = true) :
    bigW thr i c = true := by
  rw [bigW_iff] at hb ⊢
  rcases hb with hb | ⟨h1, h2⟩
  · exact Or.inl hb
  · exact Or.inr ⟨h1, le_tr h h2⟩

theorem allW_bigW_OPowTimes (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (h : α < β) :
    ∀ {X : T}, Good X → AllW (bigW (thrA k α)) (OPowTimes k β X)
  | Z, _ => trivial
  | P i c b, hX => by
      rw [OPowTimes_P k β i c b (cnt_logA_of_good hX)]
      refine ⟨?_, allW_bigW_OPowTimes k hα hβ h hX.tail⟩
      rw [bigW_iff]
      refine Or.inr ⟨Nat.le_refl 1, ?_⟩
      have hβ0 : β ≠ Z := fun e => not_lt_Z' _ (e ▸ h)
      rw [exp_OGd hβ (OG_ne_Z (fun _ => hβ0)) (cnt_logA_of_good hX)]
      unfold thrA
      rw [thr_eq k hα]
      exact le_tr (OG_succ_le k hα hβ h) (le_add_right' _ _)

theorem phi_fix (k : Nat) {α β ξ : T} (hα : Good α) (hβ : Good β) (hξ : Good ξ)
    (_hk : k = 0 → α ≠ Z) (h : α < β) : phi k α (phi k β ξ) = phi k β ξ := by
  obtain ⟨Y, hY, hYall, hBY⟩ : ∃ Y, phi k β ξ = P 0 Y Z ∧ AllW (bigW (thrA k α)) Y ∧
      alphaHead k α < Y := by
    by_cases hA : AbsP k β ξ
    · obtain ⟨i, d, b, rfl, hlt⟩ := hA
      refine ⟨_, phi_eq_abs k β hlt, ?_, ?_⟩
      · apply AllW.add
        · exact AllW.imp (fun i c hb => bigW_of_le (thrA_le k hα hβ h) hb) (takeW_all _ d)
        · apply allW_bigW_OPowTimes k hα hβ h
          split
          · exact hξ.tail
          · exact hξ
      · exact lt_of_le_of_lt' (alphaHead_le k hα hβ (le_of_lt' h))
          (lt_of_lt_of_le' hlt (le_add_right' _ _))
    · refine ⟨_, phi_eq_dflt k β ξ hA, ?_, ?_⟩
      · apply AllW.add
        · cases β with
          | Z => trivial
          | P j d b =>
              rw [alphaHead_P]
              exact AllW.imp (fun i c hp => predA_to_bigW k hα hp) (takeW_all _ d)
        · exact allW_bigW_OPowTimes k hα hβ h (good_coefX hξ)
      · by_cases hpX : pureB k β = true ∧ ξ = Z
        · obtain ⟨hp, rfl⟩ := hpX
          have hc : coefX k β Z = Z := by simp [coefX, hp]
          rw [hc, OPowTimes_Z, T.add_Z]
          obtain ⟨hB0, hβe⟩ := pureB_true hp
          cases α with
          | Z =>
              show Z < alphaHead k β
              cases hB : alphaHead k β with
              | Z => exact absurd hB hB0
              | P _ _ _ => exact Z_lt_P' _ _ _
          | P i d b =>
              rw [alphaHead_P]
              have hi := hα.idx; subst hi
              have hd : d < alphaHead k β := by
                rw [hβe] at h
                rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
                · exact absurd h' (Nat.lt_irrefl _)
                · exact h'
                · exact absurd h' (not_lt_Z' _)
              exact lt_of_le_of_lt' (takeW_prefix_le _ d) hd
        · apply lt_of_le_of_lt' (alphaHead_le k hα hβ (le_of_lt' h))
          apply lt_add_of_ne
          apply OPowTimes_ne_Z
          apply coefX_ne_Z
          cases hp : pureB k β
          · exact Or.inr rfl
          · left; intro hξ0; exact hpX ⟨hp, hξ0⟩
  have hD : headD k α Y = Y := takeW_of_all _ _ hYall
  have hlt : alphaHead k α < headD k α Y := by rw [hD]; exact hBY
  rw [hY, phi_eq_abs k α hlt, hD, if_pos rfl, OPowTimes_Z, T.add_Z]

theorem allW_of_headD_eq {k : Nat} {a d Pre r : T} (hr : headD k a d = T.add Pre r) :
    AllW (bigW (thrA k a)) r := by
  have := takeW_all (bigW (thrA k a)) d
  rw [show takeW (bigW (thrA k a)) d = headD k a d from rfl, hr] at this
  exact AllW.add_right this

theorem phi_lt_phi (k : Nat) (a : T) {ξ ξ' : T} (ha : Good a) (hξ : Good ξ) (hξ' : Good ξ')
    (hk : k = 0 → a ≠ Z) (h : ξ < ξ') : phi k a ξ < phi k a ξ' := by
  cases ξ' with
  | Z => exact absurd h (not_lt_Z' _)
  | P j d' b' =>
      have hj := hξ'.idx; subst hj
      by_cases hA : AbsP k a ξ
      · obtain ⟨i, d, b, rfl, hlt⟩ := hA
        have hi := hξ.idx; subst hi
        have hdd : d ≤ d' := P0_le_P0_iff.mp (head_le_of_P_lt h)
        have hDD : headD k a d ≤ headD k a d' := takeW_le_takeW (upW_bigW _) hdd
        have hlt' : alphaHead k a < headD k a d' := lt_of_lt_of_le' hlt hDD
        rw [phi_eq_abs k a hlt, phi_eq_abs k a hlt']
        apply T.Lt.p_mid
        rcases hDD with hDD | hDD
        · apply pre_lt (thr := thrA k a) _ hDD (fun r hr => allW_of_headD_eq hr)
          apply expBelow_OPowTimes k ha hk
          split
          · exact hξ.tail
          · exact hξ
        · rw [hDD]
          apply (add_lt_add_left_iff _).mpr
          have hD'le : headD k a d' ≤ d' := takeW_prefix_le _ d'
          have hDle : headD k a d ≤ d := takeW_prefix_le _ d
          by_cases h1 : d = headD k a d'
          · by_cases h2 : d' = headD k a d'
            · rw [if_pos h1, if_pos h2]
              have hdd' : d = d' := h1.trans h2.symm
              subst hdd'
              apply OPowTimes_lt k a hξ.tail hξ'.tail
              rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
              · exact absurd h' (Nat.lt_irrefl _)
              · exact absurd h' (lt_irr _)
              · exact h'
            · rw [if_pos h1, if_neg h2]
              apply OPowTimes_lt k a hξ.tail hξ'
              apply lt_of_head_lt
              refine lt_of_le_of_lt' hξ.desc.hd ?_
              show P 0 d Z < P 0 d' Z
              apply T.Lt.p_mid
              rw [h1]
              rcases hD'le with h' | h'
              · exact h'
              · exact absurd h'.symm h2
          · by_cases h2 : d' = headD k a d'
            · exfalso
              rw [← hDD] at h2
              rcases hDle with h' | h'
              · exact not_lt_of_le' hdd (h2 ▸ h')
              · exact h1 (h'.symm.trans hDD)
            · rw [if_neg h1, if_neg h2]
              exact OPowTimes_lt k a hξ hξ' h
      · rw [phi_eq_dflt k a _ hA]
        by_cases hA' : AbsP k a (P 0 d' b')
        · obtain ⟨j', d'', b'', he, hlt'⟩ := hA'
          injection he with _ h1 h2
          subst h1 h2
          rw [phi_eq_abs k a hlt']
          apply T.Lt.p_mid
          exact pre_lt (thr := thrA k a) _ hlt' (fun r hr => allW_of_headD_eq hr)
            (expBelow_OPowTimes k ha hk (good_coefX hξ))
        · rw [phi_eq_dflt k a _ hA']
          apply T.Lt.p_mid
          apply (add_lt_add_left_iff _).mpr
          apply OPowTimes_lt k a (good_coefX hξ) (good_coefX hξ')
          unfold coefX
          split
          · exact h
          · exact onePlus_lt hξ hξ' h

theorem headBelow_dropW (thr d : T) : HeadBelow thr (dropW (bigW thr) d) := by
  intro i e r he
  rcases dropW_head (bigW thr) d with h0 | ⟨i', c', rr', h1, h2⟩
  · rw [h0] at he; cases he
  · rw [h1] at he
    injection he with e1 e2 _
    rw [e1, e2] at h2
    exact headBelow_of_not_big (r := r) h2 i e r rfl

theorem coefX_cases {k : Nat} {a ξ dX rX : T} (h : coefX k a ξ = P 0 dX rX) :
    dX = Z ∨ ξ = P 0 dX rX := by
  unfold coefX at h
  split at h
  · exact Or.inr h
  · cases ξ with
    | Z => injection h with _ h2 _; exact Or.inl h2.symm
    | P i d b =>
        cases i with
        | succ i => exact Or.inr h
        | zero =>
            cases d with
            | Z => injection h with _ h2 _; exact Or.inl h2.symm
            | P _ _ _ => exact Or.inr h

theorem Z_lt_of_head_le {e Y : T} (h : P 1 e Z ≤ Y) : Z < Y := lt_of_lt_of_le' (Z_lt_P' _ _ _) h

theorem good_phi (k : Nat) (a ξ : T) (ha : Good a) (hξ : Good ξ) (hk : k = 0 → a ≠ Z) :
    Good (phi k a ξ) := by
  by_cases hA : AbsP k a ξ
  · obtain ⟨i, d, b, rfl, hlt⟩ := hA
    have hi := hξ.idx; subst hi
    rw [phi_eq_abs k a hlt]
    refine ⟨?_, rfl, trivial⟩
    have hDall : AllW (bigW (thrA k a)) (headD k a d) := takeW_all _ d
    have hdec : d = T.add (headD k a d) (dropW (bigW (thrA k a)) d) :=
      (takeW_add_dropW _ d).symm
    have hK1 : ∀ O, ∀ da ra, a = P 0 da ra → da < T.add (headD k a d) O := by
      intro O da ra hae
      subst hae
      have := K1_lt (O := O) (W := Z) k ha hk (Or.inr ⟨hlt, fun r hr => allW_of_headD_eq hr⟩)
      rwa [T.add_Z] at this
    by_cases hdD : d = headD k a d
    · rw [if_pos hdD]
      apply nf_main k ha hk hξ.tail (isNF1_head hξ.nf) ⟨_, hdec⟩ hDall
      cases hb : b with
      | Z => intro x hx; rw [OPowTimes_Z] at hx; exact absurd hx List.not_mem_nil
      | P j db rb =>
          have hbG : Good (P j db rb) := hb ▸ hξ.tail
          have hj := hbG.idx; subst hj
          apply comps_lt k ha hk hbG (head_le_Y k ha hk hbG hDall)
          · exact hK1 _
          · have hdb : db ≤ d := by
              have := hξ.desc.hd
              rw [hb] at this
              exact P0_le_P0_iff.mp this
            refine lt_of_le_of_lt' hdb ?_
            conv => lhs; rw [hdD]
            exact lt_add_of_ne _ (OPowTimes_ne_Z nofun)
    · rw [if_neg hdD]
      apply nf_main k ha hk hξ (isNF1_head hξ.nf) ⟨_, hdec⟩ hDall
      apply comps_lt k ha hk hξ (head_le_Y k ha hk hξ hDall)
      · exact hK1 _
      · exact nb_lt k ha hk hξ (AllW.unc_bigW hDall) hdec
  · rw [phi_eq_dflt k a ξ hA]
    refine ⟨?_, rfl, trivial⟩
    have hall : AllW (bigW (thrA k a)) (alphaHead k a) := by
      cases a with
      | Z => trivial
      | P j d b =>
          rw [alphaHead_P]
          exact AllW.imp (fun i c hp => predA_to_bigW k ha hp) (takeW_all _ d)
    obtain ⟨h0, hh0, hpre⟩ : ∃ h0, T.isNF1 (P 0 h0 Z) ∧ ∃ rest, h0 = T.add (alphaHead k a) rest := by
      cases a with
      | Z => exact ⟨Z, good_one.nf, Z, rfl⟩
      | P j d b =>
          have hj := ha.idx; subst hj
          exact ⟨d, isNF1_head ha.nf, _, by rw [alphaHead_P, takeW_add_dropW]⟩
    apply nf_main k ha hk (good_coefX hξ) hh0 hpre hall
    cases hX : coefX k a ξ with
    | Z => intro x hx; rw [OPowTimes_Z] at hx; exact absurd hx List.not_mem_nil
    | P j dX rX =>
        have hXG : Good (P j dX rX) := hX ▸ good_coefX hξ
        have hj := hXG.idx; subst hj
        have hY1 := head_le_Y k ha hk hXG hall
        apply comps_lt k ha hk hXG hY1
        · intro da ra hae
          subst hae
          have := K1_lt (O := OPowTimes k (P 0 da ra) (P 0 dX rX)) (W := Z) k ha hk
            (Or.inl ⟨rfl, OPowTimes_ne_Z nofun, ?_⟩)
          · rwa [T.add_Z] at this
          · intro j e r hO
            rw [OPowTimes_P k _ 0 dX rX (cnt_logA_of_good hXG)] at hO
            injection hO with h1 h2 _
            subst h1 h2
            refine ⟨rfl, ?_⟩
            rw [exp_OGd ha (OG_ne_Z hk) (cnt_logA_of_good hXG)]
            exact le_add_right' _ _
        · rcases coefX_cases hX with h0 | hξe
          · rw [h0] at hY1 ⊢; exact Z_lt_of_head_le hY1
          · subst hξe
            have hdec : dX = T.add (headD k a dX) (dropW (bigW (thrA k a)) dX) :=
              (takeW_add_dropW _ dX).symm
            have hle : headD k a dX ≤ alphaHead k a :=
              le_of_not_lt' (fun h' => hA ⟨0, dX, rX, rfl, h'⟩)
            rcases hle with hle | hle
            · conv => lhs; rw [hdec]
              apply pre_lt' (thr := thrA k a) _ hle _ (headBelow_dropW _ _)
              intro r hr
              have := hall
              rw [hr] at this
              exact AllW.add_right this
            · rw [hle] at hdec
              exact nb_lt k ha hk hξ (AllW.unc_bigW hall) hdec

end Sem
