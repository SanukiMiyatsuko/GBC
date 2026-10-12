import Mbekworm.Sequence.SemFacts
import Mbekworm.Sequence.ParentSearch

/-!
# Continuity and fixed-point limits

Continuity of `ω^y`, `Ω^(Ω·k + a)·x` and `phi`, and the limits of the
iterations of the hyperation: `E (ω^e) (X + 1)` is the limit of
`E δ (E (ω^e) X + 1)` for `δ < ω^e`.
-/

open T GenBek

namespace Sem

/-!
## Continuity of the building blocks
-/

/-- Well-founded induction over normal forms. -/
theorem nf_induction {Q : T → Prop}
    (h : ∀ x, T.isNF1 x → (∀ y, T.isNF1 y → y < x → Q y) → Q x) : ∀ x, T.isNF1 x → Q x := by
  intro x hx
  exact T.well_founded_NF1.induction (C := fun a : T.NF1 => Q a.1) ⟨x, hx⟩
    (fun a ih => h a.1 a.2 (fun y hy hya => ih ⟨y, hy⟩ hya))

/-- Strictly monotone maps on countable normal forms are inflationary. -/
theorem infl_of_mono {f : T → T} (hg : ∀ x, Good x → Good (f x))
    (hm : ∀ x y, Good x → Good y → x < y → f x < f y) : ∀ x, Good x → x ≤ f x := by
  have key : ∀ x, T.isNF1 x → Cnt x → ¬ f x < x := by
    apply nf_induction (Q := fun x => Cnt x → ¬ f x < x)
    intro x hx ih hc hlt
    have hgx : Good x := ⟨hx, hc⟩
    have hfx := hg x hgx
    exact ih (f x) hfx.nf hlt hfx.cnt (hm (f x) x hfx hgx hlt)
  intro x hx
  exact le_of_not_lt' (key x hx.nf hx.cnt)

theorem phi_infl (k : Nat) {a : T} (ha : Good a) (hk : k = 0 → a ≠ Z) :
    ∀ ξ, Good ξ → ξ ≤ phi k a ξ :=
  infl_of_mono (fun x hx => good_phi k a x ha hx hk)
    (fun x y hx hy h => phi_lt_phi k a ha hx hy hk h)

theorem lt_add_one_le : ∀ (a b : T), b < T.add a one → b ≤ a
  | Z, b, h => by
      cases b with
      | Z => exact le_refl' _
      | P j u v =>
          exfalso
          rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
          · omega
          · exact not_lt_Z' _ h'
          · exact not_lt_Z' _ h'
  | P i x y, b, h => by
      rw [add_P] at h
      cases b with
      | Z => exact Z_le' _
      | P j u v =>
          rcases lt_inv _ _ _ _ _ _ h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
          · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h')
          · exact Or.inl (T.Lt.p_mid _ _ _ _ _ h')
          · exact P_le_P_tail (lt_add_one_le y v h')

theorem cntPart_add_unc : ∀ {Pre : T}, Unc Pre → ∀ X : T, cntPart (T.add Pre X) = cntPart X
  | Z, _, _ => rfl
  | P 0 _ _, h, _ => absurd h.1 (by omega)
  | P (i + 1) a b, h, X => by
      rw [add_P]
      show cntPart (T.add b X) = _
      exact cntPart_add_unc h.2 X

/-- `s` is cofinal below `x`. -/
def Cof (x : T) {ι : Type} (s : ι → T) : Prop := ∀ b, T.isNF1 b → b < x → ∃ n, b ≤ s n

/-- Limit: nonzero and not ending with `1`. -/
def Lim (ξ : T) : Prop := ξ ≠ Z ∧ ∀ y, ξ ≠ T.add y one

theorem Lim.pos {ξ : T} (hl : Lim ξ) : Z < ξ := by
  cases ξ with
  | Z => exact absurd rfl hl.1
  | P _ _ _ => exact Z_lt_P' _ _ _

theorem Lim.succ_lt {ξ y : T} (hξ : Good ξ) (hl : Lim ξ) (hy : Good y) (h : y < ξ) :
    T.add y one < ξ := by
  rcases lt_total_thm (T.add y one) ξ with h' | h' | h'
  · exact h'
  · exfalso
    rcases lt_add_one_le y ξ h' with h'' | h''
    · exact not_lt_of_le' (Or.inl h'') h
    · rw [h''] at h; exact lt_irr _ h
  · exact absurd h'.symm (hl.2 y)

theorem good_add_one {y : T} (hy : Good y) : Good (T.add y one) := by
  refine ⟨?_, Cnt.add hy.cnt good_one.cnt⟩
  rw [← oadd_one]
  exact isNF1_oadd hy.nf good_one.nf

/-! ### `log` and `ω^x` are mutually inverse -/

theorem logA_omegaArg {y : T} (hy : Good y) : logA (omegaArg y) = y := by
  cases y with
  | Z => rfl
  | P i e b =>
      have hi := hy.idx; subst hi
      have hen := isNF1_head hy.nf
      simp only [omegaArg]
      by_cases hU : uncPart e = Z
      · rw [if_pos hU, logA_of_unc_Z]
        rfl
      · rw [if_neg hU]
        have hu := unc_uncPart e
        have hb := hy.cnt.tail
        by_cases hR : cntPart e = Z
        · rw [if_pos hR]
          have he : e = uncPart e := by
            have h2 := uncPart_add_cntPart e; rw [hR, T.add_Z] at h2; exact h2.symm
          rw [logA_of_unc_ne (by rw [uncPart_add_unc hu]; intro h'; exact hU (add_eq_Z_iff.mp h').1),
            uncPart_add_unc hu, cntPart_add_unc hu]
          have hUb : uncPart b = Z := by
            rcases cnt_head_of_cnt hb with rfl | ⟨a', b', rfl⟩ <;> rfl
          rw [hUb, T.add_Z, ← he]
          rcases cnt_head_of_cnt hb with rfl | ⟨a', b', rfl⟩
          · rw [cntPart_Z', oadd_Z_right]
          · show oadd (P 0 e Z) (P 0 a' b') = P 0 e (P 0 a' b')
            rw [oadd_P_of_not_lt (not_lt_of_le' (isNF1_hd hy.nf)), oadd_Z_left]
        · rw [if_neg hR]
          rw [logA_of_unc_ne (by rw [uncPart_add_unc hu]; intro h'; exact hU (add_eq_Z_iff.mp h').1),
            uncPart_add_unc hu, cntPart_add_unc hu]
          show oadd (P 0 (T.add (uncPart e) (uncPart (P 0 e b))) Z) (cntPart (P 0 e b)) = P 0 e b
          rw [show uncPart (P 0 e b) = Z from rfl, T.add_Z, show cntPart (P 0 e b) = P 0 e b from rfl]
          apply oadd_P_of_lt
          show P 0 (uncPart e) Z < P 0 e Z
          apply T.Lt.p_mid
          conv => rhs; rw [← uncPart_add_cntPart e]
          exact lt_add_of_ne _ hR
where
  cntPart_Z' : cntPart Z = Z := rfl

theorem omegaArg_logA {c : T} (hc : T.isNF1 (P 0 c Z)) : omegaArg (logA c) = c := by
  have hcU := uncPart_add_cntPart c
  by_cases hU : uncPart c = Z
  · rw [logA_of_unc_Z hU]
    cases c with
    | Z => rfl
    | P i c1 c2 =>
        cases i with
        | succ i => simp only [uncPart] at hU; cases hU
        | zero =>
            simp only [omegaArg]
            have hc1 : c1 < P 0 c1 c2 := isNF1_G hc c1 (by rw [G1_P0]; simp)
            have hcnt : Cnt c1 := Cnt_of_lt_Om (isNF1_desc (isNF1_arg (isNF1_arg hc)))
              (lt_tr hc1 (T.Lt.p_head _ _ _ _ _ _ Nat.zero_lt_one))
            rw [if_pos]
            rcases cnt_head_of_cnt hcnt with h | ⟨a', b', h⟩ <;> rw [h] <;> rfl
  · rw [logA_of_unc_ne hU]
    have hu := unc_uncPart c
    rcases cntPart_head c with hR | ⟨r, r2, hr⟩
    · rw [hR, oadd_Z_right]
      show (if uncPart (uncPart c) = Z then _ else if cntPart (uncPart c) = Z then
        T.add (uncPart (uncPart c)) Z else _) = c
      rw [hu.uncPart, if_neg hU, if_pos hu.cntPart, T.add_Z]
      have h2 := hcU; rw [hR, T.add_Z] at h2; exact h2
    · rw [hr]
      by_cases hlt : P 0 (uncPart c) Z < T.head (P 0 r r2)
      · rw [oadd_P_of_lt hlt]
        have hUr : uncPart c < r := P0_lt_P0_iff.mp hlt
        have hrc : r < c := isNF1_G hc r (by rw [← hcU, G1_add, hr, G1_P0]; simp)
        rw [← hcU] at hrc
        obtain ⟨r', hr'⟩ := between_prefix (Or.inl hUr) hrc
        have hr'lt : r' < cntPart c := by rw [hr'] at hrc; exact (add_lt_add_left_iff _).mp hrc
        rw [hr] at hr'lt
        have hr'cnt : r' = Z ∨ ∃ a b, r' = P 0 a b := by
          cases r' with
          | Z => exact Or.inl rfl
          | P j a b =>
              rcases lt_inv _ _ _ _ _ _ hr'lt with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
              · exact absurd h (Nat.not_lt_zero _)
              · exact Or.inr ⟨a, b, rfl⟩
              · exact Or.inr ⟨a, b, rfl⟩
        have hr'0 : r' ≠ Z := by
          intro e; rw [e, T.add_Z] at hr'; rw [hr'] at hUr; exact lt_irr _ hUr
        simp only [omegaArg]
        have h1 : uncPart r = uncPart c := by
          rw [hr', uncPart_add_unc hu]
          rcases hr'cnt with h | ⟨a, b, h⟩
          · exact absurd h hr'0
          · rw [h]; show T.add (uncPart c) Z = _; rw [T.add_Z]
        have h2 : cntPart r = r' := by
          rw [hr', cntPart_add_unc hu]
          rcases hr'cnt with h | ⟨a, b, h⟩
          · exact absurd h hr'0
          · rw [h]; rfl
        rw [h1, if_neg hU, h2, if_neg hr'0, ← hr, hcU]
      · rw [oadd_P_of_not_lt hlt, oadd_Z_left]
        show (if uncPart (uncPart c) = Z then _ else if cntPart (uncPart c) = Z then
          T.add (uncPart (uncPart c)) (P 0 r r2) else _) = c
        rw [hu.uncPart, if_neg hU, if_pos hu.cntPart, ← hr, hcU]

theorem omegaPow_logA {c : T} (hc : T.isNF1 (P 0 c Z)) : omegaPow (logA c) = P 0 c Z := by
  rw [omegaPow_eq, omegaArg_logA hc]

theorem omegaPow_cont {ξ : T} (hξ : Good ξ) (hl : Lim ξ) {ι : Type} {s : ι → T} (hs : ∀ n, Good (s n))
    (hcof : Cof ξ s) : Cof (omegaPow ξ) (fun n => omegaPow (s n)) := by
  intro b hb hlt
  cases b with
  | Z =>
      obtain ⟨n0, -⟩ := hcof Z T.isNF1.z hl.pos
      exact ⟨n0, Z_le' _⟩
  | P i c r =>
      rw [omegaPow_eq] at hlt
      obtain ⟨rfl, hcA⟩ := lt_P0 hlt
      have hcn := isNF1_head hb
      have hX0 := good_logA hcn
      have hX0ξ : logA c < ξ := by
        rcases lt_total_thm (logA c) ξ with h | h | h
        · exact h
        · exfalso
          have := omegaPow_lt_omegaPow hξ hX0 h
          rw [omegaPow_logA hcn, omegaPow_eq] at this
          exact not_lt_of_le' (Or.inl (T.Lt.p_mid _ _ _ _ _ hcA)) this
        · exfalso
          have := congrArg omegaPow h
          rw [omegaPow_logA hcn, omegaPow_eq] at this
          injection this with _ h'
          rw [h'] at hcA; exact lt_irr _ hcA
      have hsucc := hl.succ_lt hξ hX0 hX0ξ
      obtain ⟨n, hn⟩ := hcof _ (good_add_one hX0).nf hsucc
      refine ⟨n, le_tr (Or.inl ?_) (omegaPow_le_omegaPow (good_add_one hX0) (hs n) hn)⟩
      have h3 := omegaPow_lt_omegaPow hX0 (good_add_one hX0) (lt_add_of_ne _ nofun)
      rw [omegaPow_logA hcn, omegaPow_eq] at h3
      rw [omegaPow_eq]
      exact P_lt_P_of_head_lt _ _ h3

/-! ### Repeated summands -/

theorem copies_decomp (e : T) : ∀ {c : T}, Desc c → T.head c ≤ P 1 e Z →
    ∃ N t, c = T.add (copies e N) t ∧ (t = Z ∨ T.head t < P 1 e Z)
  | Z, _, _ => ⟨0, Z, rfl, Or.inl rfl⟩
  | P i x r, hd, hh => by
      rcases hh with hh | hh
      · exact ⟨0, P i x r, rfl, Or.inr hh⟩
      · simp only [T.head] at hh
        injection hh with h1 h2
        subst h1 h2
        obtain ⟨N, t, ht, htl⟩ := copies_decomp x hd.tail hd.hd
        exact ⟨N + 1, t, by rw [ht]; show _ = T.add (P 1 x (copies x N)) t; rw [add_P], htl⟩

theorem copies_add_lt (e t : T) (ht : t = Z ∨ T.head t < P 1 e Z) :
    ∀ N, T.add (copies e N) t < copies e (N + 1)
  | 0 => by
      rcases ht with rfl | ht
      · exact Z_lt_P' _ _ _
      · exact lt_of_head_lt ht
  | N + 1 => by
      show T.add (P 1 e (copies e N)) t < P 1 e (copies e (N + 1))
      rw [add_P]
      exact T.Lt.p_tail _ _ _ _ (copies_add_lt e t ht N)

/-- `N` copies of the principal term `P 0 x Z`. -/
def rep0 (x : T) : Nat → T
  | 0 => Z
  | N + 1 => P 0 x (rep0 x N)

theorem good_rep0 {x : T} (hx : Good (P 0 x Z)) : ∀ N, Good (rep0 x N)
  | 0 => good_Z
  | N + 1 => by
      refine ⟨(isNF1_P_iff 0 x _).mpr ⟨hx.nf, (good_rep0 hx N).nf, ?_⟩, rfl, (good_rep0 hx N).cnt⟩
      cases N with
      | zero => exact Z_le' _
      | succ N => exact le_refl' _

theorem OPowTimes_rep0 (k : Nat) (a : T) {lm : T} (hl : Good lm) :
    ∀ N, OPowTimes k a (rep0 (omegaArg lm) N) = copies (T.add (OGd k a) lm) N
  | 0 => rfl
  | N + 1 => by
      have hg : Good (P 0 (omegaArg lm) Z) := by rw [← omegaPow_eq]; exact good_omegaPow hl
      show OPowTimes k a (P 0 (omegaArg lm) (rep0 (omegaArg lm) N)) = _
      rw [OPowTimes_P k a 0 _ _ (by rw [logA_omegaArg hl]; exact hl.cnt), logA_omegaArg hl,
        OPowTimes_rep0 k a hl N]
      rfl

theorem finite_of_one_head : ∀ {ξ : T}, Good ξ → (∃ r, ξ = P 0 Z r) → ∃ y, ξ = T.add y one
  | Z, _, ⟨r, h⟩ => by cases h
  | P i e rest, hξ, ⟨r, h⟩ => by
      injection h with h1 h2 _
      subst h1 h2
      cases rest with
      | Z => exact ⟨Z, rfl⟩
      | P j e' r' =>
          have hj := hξ.tail.idx; subst hj
          have he' : e' = Z := by
            rcases P0_le_P0_iff.mp hξ.desc.hd with h | h
            · exact absurd h (not_lt_Z' _)
            · exact h
          subst he'
          obtain ⟨y, hy⟩ := finite_of_one_head hξ.tail ⟨r', rfl⟩
          exact ⟨P 0 Z y, by rw [hy, add_P]⟩

theorem Lim.one_lt {ξ : T} (hξ : Good ξ) (hl : Lim ξ) : one < ξ := by
  cases ξ with
  | Z => exact absurd rfl hl.1
  | P i e rest =>
      have hi := hξ.idx; subst hi
      cases e with
      | Z =>
          obtain ⟨y, hy⟩ := finite_of_one_head hξ ⟨rest, rfl⟩
          exact absurd hy (hl.2 y)
      | P _ _ _ => exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)

theorem Lim.tail {e r : T} (hl : Lim (P 0 e r)) (hr : r ≠ Z) : Lim r :=
  ⟨hr, fun y hy => hl.2 (P 0 e y) (by rw [hy, add_P])⟩

/-- **Continuity of `OPowTimes`** at limits. -/
theorem OPT_cont (k : Nat) {a : T} (ha : Good a) :
    ∀ {ξ : T}, Good ξ → Lim ξ → ∀ {c : T}, T.isNF1 c → c < OPowTimes k a ξ →
      ∃ X, Good X ∧ X < ξ ∧ c < OPowTimes k a X
  | Z, _, hl, _, _, _ => absurd rfl hl.1
  | P i e rest, hξ, hl, c, hc, hlt => by
      have hi := hξ.idx; subst hi
      have hone := hl.one_lt hξ
      have hOne : OPowTimes k a one = P 1 (OGd k a) Z := by
        rw [show one = P 0 Z Z from rfl, OPowTimes_P k a 0 Z Z trivial, logA_Z, T.add_Z]; rfl
      rw [OPowTimes_P k a 0 e rest (cnt_logA_of_good hξ)] at hlt
      cases c with
      | Z => exact ⟨one, good_one, hone, by rw [hOne]; exact Z_lt_P' _ _ _⟩
      | P j x c3 =>
          rcases lt_inv _ _ _ _ _ _ hlt with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
          · refine ⟨one, good_one, hone, ?_⟩
            rw [hOne]; exact T.Lt.p_head _ _ _ _ _ _ h'
          · by_cases hxO : x < OGd k a
            · refine ⟨one, good_one, hone, ?_⟩
              rw [hOne]; exact T.Lt.p_mid _ _ _ _ _ hxO
            · obtain ⟨lam, hlam⟩ := between_prefix (le_of_not_lt' hxO) h'
              have hlamlt : lam < logA e := by rw [hlam] at h'; exact (add_lt_add_left_iff _).mp h'
              have hxn := isNF1_arg hc
              rw [hlam] at hxn
              have hlamn := isNF1_of_add_right hxn
              have hle := good_logA (isNF1_head hξ.nf)
              have hlamg : Good lam := ⟨hlamn, Cnt_of_lt_Om (isNF1_desc hlamn)
                (lt_tr hlamlt (Cnt_lt_Om hle.cnt))⟩
              have hcd : Desc (P 1 x c3) := isNF1_desc hc
              rw [hlam] at hcd
              obtain ⟨N, t, ht, htl⟩ := copies_decomp (T.add (OGd k a) lam) hcd (le_refl' _)
              have hg0 : Good (P 0 (omegaArg lam) Z) := by
                rw [← omegaPow_eq]; exact good_omegaPow hlamg
              refine ⟨rep0 (omegaArg lam) (N + 1), good_rep0 hg0 (N + 1), ?_, ?_⟩
              · apply lt_of_head_lt
                show P 0 (omegaArg lam) Z < P 0 e Z
                have := omegaPow_lt_omegaPow hlamg hle hlamlt
                rwa [omegaPow_logA (isNF1_head hξ.nf), omegaPow_eq] at this
              · rw [OPowTimes_rep0 k a hlamg, hlam, ht]
                exact copies_add_lt _ t htl N
          · cases rest with
            | Z => exact absurd h' (not_lt_Z' _)
            | P j' e' r' =>
                obtain ⟨X', hX', hX'r, hcX'⟩ :=
                  OPT_cont k ha hξ.tail (hl.tail nofun) (isNF1_tail hc) h'
                refine ⟨P 0 e X', ?_, T.Lt.p_tail _ _ _ _ hX'r, ?_⟩
                · refine ⟨(isNF1_P_iff 0 e X').mpr ⟨isNF1_head hξ.nf, hX'.nf, ?_⟩, rfl, hX'.cnt⟩
                  rcases head_le_of_lt hX'r with h | h
                  · exact le_tr (Or.inl h) hξ.desc.hd
                  · rw [h]; exact hξ.desc.hd
                · rw [OPowTimes_P k a 0 e X' (cnt_logA_of_good hξ)]
                  exact T.Lt.p_tail _ _ _ _ hcX'

/-! ### Continuity of `phi` in its second argument -/

theorem coefX_of_lim {k : Nat} {a ξ : T} (hξ : Good ξ) (hl : Lim ξ) : coefX k a ξ = ξ := by
  unfold coefX
  split
  · rfl
  · cases ξ with
    | Z => exact absurd rfl hl.1
    | P i e b =>
        have hi := hξ.idx; subst hi
        cases e with
        | Z =>
            obtain ⟨y, hy⟩ := finite_of_one_head hξ ⟨b, rfl⟩
            exact absurd hy (hl.2 y)
        | P _ _ _ => rfl

theorem le_onePlus {ξ : T} (hξ : Good ξ) : ξ ≤ onePlus ξ := by
  cases ξ with
  | Z => exact Or.inl (Z_lt_P' _ _ _)
  | P i e b =>
      have hi := hξ.idx; subst hi
      cases e with
      | Z => exact Or.inl (T.Lt.p_tail _ _ _ _ (tail_lt_of_desc hξ.desc))
      | P _ _ _ => exact le_refl' _

theorem le_coefX {k : Nat} {a ξ : T} (hξ : Good ξ) : ξ ≤ coefX k a ξ := by
  unfold coefX; split
  · exact le_refl' _
  · exact le_onePlus hξ

theorem absP_mono {k : Nat} {a ξ ξ' : T} (hξ : Good ξ) (hξ' : Good ξ') (h : ξ ≤ ξ')
    (hA : AbsP k a ξ) : AbsP k a ξ' := by
  obtain ⟨i, d, b, rfl, hlt⟩ := hA
  have hi := hξ.idx; subst hi
  cases ξ' with
  | Z =>
      rcases h with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P j d' b' =>
      have hj := hξ'.idx; subst hj
      have hdd : d ≤ d' := by
        rcases h with h | h
        · exact P0_le_P0_iff.mp (head_le_of_P_lt h)
        · injection h with _ h; exact Or.inr h
      exact ⟨0, d', b', rfl, lt_of_lt_of_le' hlt (takeW_le_takeW (upW_bigW _) hdd)⟩

theorem headD_idem (k : Nat) (a d : T) : headD k a (headD k a d) = headD k a d :=
  takeW_of_all _ _ (takeW_all _ d)

theorem headD_le (k : Nat) (a d : T) : headD k a d ≤ d := takeW_prefix_le _ d

/-- Inside the region of a fixed point `ψ₀(D)`, `phi` keeps the same absorbed part. -/
theorem abs_region {k : Nat} {a d b0 x : T} (hBD : alphaHead k a < headD k a d) (hx : Good x)
    (h1 : P 0 (headD k a d) Z ≤ x) (h2 : x < P 0 d b0) :
    ∃ dx bx, x = P 0 dx bx ∧ headD k a dx = headD k a d := by
  cases x with
  | Z =>
      rcases h1 with h | h
      · exact absurd h (not_lt_Z' _)
      · cases h
  | P i dx bx =>
      have hi := hx.idx; subst hi
      refine ⟨dx, bx, rfl, ?_⟩
      have hD1 : headD k a d ≤ dx := by
        rcases h1 with h | h
        · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, h', _⟩
          · exact absurd h' (Nat.lt_irrefl _)
          · exact Or.inl h'
          · exact Or.inr h'
        · injection h with _ h; exact Or.inr h
      have hD2 : dx ≤ d := P0_le_P0_iff.mp (head_le_of_P_lt h2)
      have e1 := takeW_le_takeW (upW_bigW (thrA k a)) hD1
      have e2 := takeW_le_takeW (upW_bigW (thrA k a)) hD2
      rw [show takeW (bigW (thrA k a)) (headD k a d) = headD k a d from headD_idem k a d] at e1
      exact le_antisymm' e2 e1

theorem le_oadd_P0 (D X : T) (hX : Good X) :
    P 0 D Z ≤ oadd (P 0 D Z) X ∧ X ≤ oadd (P 0 D Z) X := by
  refine ⟨?_, le_oadd_right _ _ hX.desc⟩
  rw [oadd_P]
  split
  · rename_i h
    exact Or.inl (lt_of_head_lt h)
  · rw [oadd_Z_left]; exact P_le_P_tail (Z_le' _)

theorem phi_cont (k : Nat) {a ξ : T} (ha : Good a) (hk : k = 0 → a ≠ Z) (hξ : Good ξ)
    (hl : Lim ξ) {ι : Type} {s : ι → T} (hs : ∀ n, Good (s n)) (hslt : ∀ n, s n < ξ) (hcof : Cof ξ s) :
    Cof (phi k a ξ) (fun n => phi k a (s n)) := by
  intro b hb hlt
  cases b with
  | Z =>
      obtain ⟨n0, -⟩ := hcof Z T.isNF1.z hl.pos
      exact ⟨n0, Z_le' _⟩
  | P i c r =>
      by_cases hA : AbsP k a ξ
      · obtain ⟨i0, d, b0, rfl, hBD⟩ := hA
        have hi0 := hξ.idx; subst hi0
        by_cases hfix : d = headD k a d ∧ b0 = Z
        · have hphi : phi k a (P 0 d b0) = P 0 d b0 := by
            rw [phi_eq_abs k a hBD, if_pos hfix.1, hfix.2, OPowTimes_Z, T.add_Z, ← hfix.1]
          rw [hphi] at hlt
          obtain ⟨n, hn⟩ := hcof _ hb hlt
          exact ⟨n, le_tr hn (phi_infl k ha hk _ (hs n))⟩
        · rw [phi_eq_abs k a hBD] at hlt
          have hcY : i = 0 ∧ c < T.add (headD k a d) (OPowTimes k a
              (if d = headD k a d then b0 else P 0 d b0)) := by
            rcases lt_inv _ _ _ _ _ _ hlt with h | ⟨h, h'⟩ | ⟨_, _, h'⟩
            · exact absurd h (Nat.not_lt_zero _)
            · exact ⟨h, h'⟩
            · exact absurd h' (not_lt_Z' _)
          obtain ⟨rfl, hcY⟩ := hcY
          generalize hD : headD k a d = D at hBD hcY hfix
          have hDd : D ≤ d := hD ▸ headD_le k a d
          -- the rest of `ξ` after its fixed point
          have hRg : Good (if d = D then b0 else P 0 d b0) := by
            split
            · exact hξ.tail
            · exact hξ
          have hRl : Lim (if d = D then b0 else P 0 d b0) := by
            split
            · rename_i hdD
              have hb0 : b0 ≠ Z := fun e => hfix ⟨hdD, e⟩
              exact hl.tail hb0
            · exact hl
          have hψD : P 0 D Z < P 0 d b0 := by
            rcases hDd with h | h
            · exact T.Lt.p_mid _ _ _ _ _ h
            · subst h
              apply T.Lt.p_tail
              cases b0 with
              | Z => exact absurd ⟨rfl, rfl⟩ hfix
              | P _ _ _ => exact Z_lt_P' _ _ _
          have hψDn : T.isNF1 (P 0 D Z) := by
            rw [← hD]
            refine (isNF1_P_Z_iff 0 _).mpr ⟨?_, ?_⟩
            · have := isNF1_arg (isNF1_head hξ.nf)
              rw [← takeW_add_dropW (bigW (thrA k a)) d] at this
              exact isNF1_of_add_left this
            · intro x hx
              apply lt_prefix_of_comp hx (R := dropW (bigW (thrA k a)) d)
              rw [show T.add (headD k a d) (dropW (bigW (thrA k a)) d) = d from
                takeW_add_dropW _ d]
              apply isNF1_G (isNF1_head hξ.nf) x
              rw [← takeW_add_dropW (bigW (thrA k a)) d, G1_add]
              exact List.mem_append_left _ hx
          have hregion : ∀ n, P 0 D Z ≤ s n → ∃ R, Good R ∧
              phi k a (s n) = P 0 (T.add D (OPowTimes k a R)) Z ∧
              ∀ X, Good X → oadd (P 0 D Z) X ≤ s n → X ≤ R := by
            intro n hn
            obtain ⟨dx, bx, hsx, hdx⟩ := abs_region (hD ▸ hBD) (hs n) (hD ▸ hn) (hslt n)
            rw [hD] at hdx
            have hBD' : alphaHead k a < headD k a dx := by rw [hdx]; exact hBD
            have hsg := hs n
            rw [hsx] at hsg
            refine ⟨if dx = D then bx else P 0 dx bx, ?_, ?_, ?_⟩
            · split
              · exact hsg.tail
              · exact hsg
            · rw [hsx, phi_eq_abs k a hBD', hdx]
            · intro X hX hle
              rw [hsx] at hle
              split
              · rename_i hdxD
                subst hdxD
                rw [oadd_P] at hle
                split at hle
                · rename_i habs
                  exfalso
                  have h1 := head_le_of_lt' hle
                  exact not_lt_of_le' h1 habs
                · rw [oadd_Z_left] at hle
                  rcases hle with h | h
                  · rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
                    · exact absurd h' (Nat.lt_irrefl _)
                    · exact absurd h' (lt_irr _)
                    · exact Or.inl h'
                  · injection h with _ _ h; exact Or.inr h
              · exact le_tr (le_oadd_P0 D X hX).2 hle
          by_cases hcD : c < D
          · obtain ⟨n, hn⟩ := hcof _ hψDn hψD
            obtain ⟨R, -, hR, -⟩ := hregion n hn
            refine ⟨n, Or.inl ?_⟩
            show P 0 c r < phi k a (s n)
            rw [hR]
            exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_lt _ _ hcD)
          · obtain ⟨c'', hc''⟩ := between_prefix (le_of_not_lt' hcD) hcY
            have hc''lt : c'' < OPowTimes k a (if d = D then b0 else P 0 d b0) := by
              rw [hc''] at hcY; exact (add_lt_add_left_iff _).mp hcY
            have hc''n : T.isNF1 c'' := by
              have := isNF1_arg hb; rw [hc''] at this; exact isNF1_of_add_right this
            obtain ⟨X, hX, hXR, hcX⟩ := OPT_cont k ha hRg hRl hc''n hc''lt
            have he := good_oadd ⟨hψDn, rfl, trivial⟩ hX
            have helt : oadd (P 0 D Z) X < P 0 d b0 := by
              rw [oadd_P]
              split
              · split at hXR
                · rename_i habs hdD
                  exfalso
                  have h1 := head_le_of_lt hXR
                  exact not_lt_of_le' (le_tr h1 (by rw [← hdD]; exact hξ.desc.hd)) habs
                · exact hXR
              · rw [oadd_Z_left]
                split at hXR
                · rename_i _ hdD
                  subst hdD
                  exact T.Lt.p_tail _ _ _ _ hXR
                · rename_i _ hdD
                  rcases hDd with h | h
                  · exact T.Lt.p_mid _ _ _ _ _ h
                  · exact absurd h.symm hdD
            obtain ⟨n, hn⟩ := hcof _ he.nf helt
            obtain ⟨R, hR, hphin, hXle⟩ := hregion n (le_tr (le_oadd_P0 D X hX).1 hn)
            refine ⟨n, Or.inl ?_⟩
            show P 0 c r < phi k a (s n)
            rw [hphin, hc'']
            apply T.Lt.p_mid
            apply (add_lt_add_left_iff _).mpr
            exact lt_of_lt_of_le' hcX (OPowTimes_le k a hX hR (hXle X hX hn))
      · rw [phi_eq_dflt k a ξ hA, coefX_of_lim hξ hl] at hlt
        obtain ⟨rfl, hcY⟩ := lt_P0 hlt
        have hnA : ∀ n, ¬ AbsP k a (s n) := fun n h =>
          hA (absP_mono (hs n) hξ (Or.inl (hslt n)) h)
        by_cases hcB : c < alphaHead k a
        · obtain ⟨n0, -⟩ := hcof Z T.isNF1.z (lt_of_le_of_lt' (Z_le' one) (hl.one_lt hξ))
          refine ⟨n0, Or.inl ?_⟩
          show P 0 c r < phi k a (s n0)
          rw [phi_eq_dflt k a _ (hnA n0)]
          exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_lt _ _ hcB)
        · obtain ⟨c'', hc''⟩ := between_prefix (le_of_not_lt' hcB) hcY
          have hc''lt : c'' < OPowTimes k a ξ := by
            rw [hc''] at hcY; exact (add_lt_add_left_iff _).mp hcY
          have hc''n : T.isNF1 c'' := by
            have := isNF1_arg hb; rw [hc''] at this; exact isNF1_of_add_right this
          obtain ⟨X, hX, hXξ, hcX⟩ := OPT_cont k ha hξ hl hc''n hc''lt
          obtain ⟨n, hn⟩ := hcof _ hX.nf hXξ
          refine ⟨n, Or.inl ?_⟩
          show P 0 c r < phi k a (s n)
          rw [phi_eq_dflt k a _ (hnA n), hc'']
          apply T.Lt.p_mid
          apply (add_lt_add_left_iff _).mpr
          exact lt_of_lt_of_le' hcX (OPowTimes_le k a hX (good_coefX (hs n))
            (le_tr hn (le_coefX (hs n))))
where
  head_le_of_lt' {x y : T} (h : x ≤ y) : T.head x ≤ T.head y := by
    rcases h with h | rfl
    · exact head_le_of_lt h
    · exact le_refl' _

/-!
## Fixed-point iterations of the Veblen-type functions
-/

theorem succ_le_of_lt {x y : T} (h : x < y) : T.add x one ≤ y := by
  rcases lt_total_thm (T.add x one) y with h' | h' | h'
  · exact Or.inl h'
  · rcases lt_add_one_le x y h' with h'' | h''
    · exact absurd (lt_tr h h'') (lt_irr _)
    · rw [h''] at h; exact absurd h (lt_irr _)
  · exact Or.inr h'

/-- Cofinality of an iteration from a growth condition. -/
theorem cof_growth (Y0 Sinf : T) (S : T → T) (t : Nat → T)
    (hS : ∀ c'', T.isNF1 (P 0 (T.add Y0 c'') Z) → c'' < Sinf →
        ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧ c'' < S (T.add lam one))
    (hSm : ∀ x y, Good x → Good y → x ≤ y → S x ≤ S y)
    (ht : ∀ j, Good (t j)) (hinc : ∀ j, t j < t (j + 1))
    (hbase : ∃ j, P 0 Y0 Z ≤ t j)
    (hgrow : ∀ j, ∃ j', P 0 (T.add Y0 (S (t j))) Z ≤ t j') :
    Cof (P 0 (T.add Y0 Sinf) Z) t := by
  intro b hb
  refine nf_induction (Q := fun b => b < P 0 (T.add Y0 Sinf) Z → ∃ n, b ≤ t n) ?_ b hb
  intro b hb ih hlt
  cases b with
  | Z => exact ⟨0, Z_le' _⟩
  | P i c r =>
      obtain ⟨rfl, hc⟩ := lt_P0 hlt
      by_cases hcY : c < Y0
      · obtain ⟨j, hj⟩ := hbase
        exact ⟨j, le_tr (Or.inl (T.Lt.p_mid _ _ _ _ _ hcY)) hj⟩
      · obtain ⟨c'', rfl⟩ := between_prefix (le_of_not_lt' hcY) hc
        have hc'' : c'' < Sinf := (add_lt_add_left_iff _).mp hc
        obtain ⟨lam, hlam, hlamb, hcS⟩ := hS c'' (isNF1_head hb) hc''
        have hlb : lam < P 0 (T.add Y0 c'') r := lt_of_lt_of_le' hlamb (P_le_P_tail (Z_le' _))
        obtain ⟨j, hj⟩ := ih lam hlam.nf hlb (lt_tr hlb hlt)
        have h1 : T.add lam one ≤ t (j + 1) := succ_le_of_lt (lt_of_le_of_lt' hj (hinc j))
        obtain ⟨j', hj'⟩ := hgrow (j + 1)
        refine ⟨j', le_tr (Or.inl ?_) hj'⟩
        apply T.Lt.p_mid
        apply (add_lt_add_left_iff _).mpr
        exact lt_of_lt_of_le' hcS (hSm _ _ (good_add_one hlam) (ht (j + 1)) h1)

/-- Iteration of a function. -/
def iterT (F : T → T) (x0 : T) : Nat → T
  | 0 => x0
  | j + 1 => F (iterT F x0 j)

theorem good_iterT {F : T → T} {x0 : T} (hF : ∀ x, Good x → Good (F x)) (h0 : Good x0) :
    ∀ j, Good (iterT F x0 j)
  | 0 => h0
  | j + 1 => hF _ (good_iterT hF h0 j)

theorem le_of_inc {t : Nat → T} (hinc : ∀ j, t j < t (j + 1)) : ∀ i d, t i ≤ t (i + d)
  | _, 0 => le_refl' _
  | i, d + 1 => le_tr (le_of_inc hinc i d) (Or.inl (hinc (i + d)))

theorem P_le_P_add {Y u v : T} (h : u ≤ v) : P 0 (T.add Y u) Z ≤ P 0 (T.add Y v) Z := by
  rcases h with h | rfl
  · exact Or.inl (T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr h))
  · exact le_refl' _

/-- **Cofinality of an iteration** that has reached the shape `ψ₀(Y0 + S σ)`: if a step maps
`ψ₀(Y0 + S σ)` to `ψ₀(Y0 + S ψ₀(Y0 + S σ))`, the iteration climbs to `ψ₀(Y0 + Sinf)`. -/
theorem iter_cof {Y0 Sinf σ0 x0 : T} {S F : T → T} (Q : T → Prop) (j0 : Nat)
    (hS : ∀ c'', T.isNF1 (P 0 (T.add Y0 c'') Z) → c'' < Sinf →
        ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧ c'' < S (T.add lam one))
    (hSm : ∀ x y, x < y → S x < S y) (hF : ∀ x, Good x → Good (F x)) (hx0 : Good x0)
    (hstep : ∀ σ, Q σ → Good (P 0 (T.add Y0 (S σ)) Z) →
      F (P 0 (T.add Y0 (S σ)) Z) = P 0 (T.add Y0 (S (P 0 (T.add Y0 (S σ)) Z))) Z)
    (hQ : ∀ σ, Good (P 0 (T.add Y0 (S σ)) Z) → Q (P 0 (T.add Y0 (S σ)) Z))
    (hQ0 : Q σ0) (ht0 : iterT F x0 j0 = P 0 (T.add Y0 (S σ0)) Z) (hσt : σ0 < iterT F x0 j0)
    (hpre : ∀ j, j < j0 → iterT F x0 j < iterT F x0 (j + 1)) :
    Cof (P 0 (T.add Y0 Sinf) Z) (iterT F x0) := by
  have hg := good_iterT hF hx0
  have step : ∀ j σ, Q σ → σ < iterT F x0 j → iterT F x0 j = P 0 (T.add Y0 (S σ)) Z →
      iterT F x0 (j + 1) = P 0 (T.add Y0 (S (iterT F x0 j))) Z ∧
        iterT F x0 j < iterT F x0 (j + 1) := by
    intro j σ hQσ hlt he
    have hgx := hg j
    rw [he] at hgx
    have hn : iterT F x0 (j + 1) = P 0 (T.add Y0 (S (iterT F x0 j))) Z := by
      show F _ = _
      conv => lhs; rw [he]
      rw [hstep σ hQσ hgx, ← he]
    refine ⟨hn, ?_⟩
    rw [hn]
    conv => lhs; rw [he]
    exact T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr (hSm _ _ hlt))
  have key : ∀ d, ∃ σ, Q σ ∧ σ < iterT F x0 (j0 + d) ∧
      iterT F x0 (j0 + d) = P 0 (T.add Y0 (S σ)) Z := by
    intro d
    induction d with
    | zero => exact ⟨σ0, hQ0, hσt, ht0⟩
    | succ d ih =>
        obtain ⟨σ, hQσ, hlt, he⟩ := ih
        obtain ⟨hn, hlt'⟩ := step _ σ hQσ hlt he
        have hgx := hg (j0 + d)
        rw [he] at hgx
        exact ⟨_, he ▸ hQ σ hgx, hlt', hn⟩
  have hinc : ∀ j, iterT F x0 j < iterT F x0 (j + 1) := by
    intro j
    by_cases hj : j < j0
    · exact hpre j hj
    · obtain ⟨d, rfl⟩ : ∃ d, j = j0 + d := ⟨j - j0, by omega⟩
      obtain ⟨σ, hQσ, hlt, he⟩ := key d
      exact (step _ σ hQσ hlt he).2
  have hSm' : ∀ x y, Good x → Good y → x ≤ y → S x ≤ S y := fun x y _ _ h => by
    rcases h with h | rfl
    · exact Or.inl (hSm _ _ h)
    · exact le_refl' _
  refine cof_growth Y0 Sinf S _ hS hSm' hg hinc ⟨j0, ?_⟩ (fun j => ⟨j0 + j + 1, ?_⟩)
  · rw [ht0]
    have h := P_le_P_add (Y := Y0) (Z_le' (S σ0))
    rwa [T.add_Z] at h
  · obtain ⟨σ, hQσ, hlt, he⟩ := key j
    rw [(step _ σ hQσ hlt he).1]
    have hle := le_of_inc hinc j j0
    rw [Nat.add_comm j j0] at hle
    exact P_le_P_add (hSm' _ _ (hg _) (hg _) hle)

theorem OPowTimes_add (k : Nat) (a : T) : ∀ X Y : T,
    OPowTimes k a (T.add X Y) = T.add (OPowTimes k a X) (OPowTimes k a Y)
  | Z, _ => rfl
  | P i c b, Y => by
      rw [add_P]
      show P 1 _ (OPowTimes k a (T.add b Y)) = T.add (P 1 _ (OPowTimes k a b)) _
      rw [add_P, OPowTimes_add k a b Y]

theorem OPowTimes_one (k : Nat) (a : T) : OPowTimes k a one = P 1 (OGd k a) Z := by
  rw [show one = P 0 Z Z from rfl, OPowTimes_P k a 0 Z Z trivial, logA_Z, T.add_Z]; rfl

theorem onePlus_add_one {ξ : T} (hξ : Good ξ) : onePlus (T.add ξ one) = T.add (onePlus ξ) one := by
  cases ξ with
  | Z => rfl
  | P i e b =>
      have hi := hξ.idx; subst hi
      cases e with
      | Z => rw [add_P]; rfl
      | P _ _ _ => rw [add_P]; rfl

theorem coefX_add_one {k : Nat} {a ξ : T} (hξ : Good ξ) :
    coefX k a (T.add ξ one) = T.add (coefX k a ξ) one := by
  unfold coefX
  split
  · rfl
  · exact onePlus_add_one hξ

theorem absP_add_one_iff {k : Nat} {a ξ : T} (hξ : Good ξ) :
    AbsP k a (T.add ξ one) ↔ AbsP k a ξ := by
  cases ξ with
  | Z =>
      constructor
      · rintro ⟨i, d, b, he, hlt⟩
        injection he with _ h2 _
        subst h2
        exact absurd hlt (not_lt_of_le' (Z_le' _))
      · rintro ⟨_, _, _, he, _⟩; cases he
  | P i e b =>
      rw [add_P]
      constructor
      · rintro ⟨i', d, b', he, hlt⟩
        injection he with h1 h2 _
        subst h1 h2
        exact ⟨_, _, _, rfl, hlt⟩
      · rintro ⟨i', d, b', he, hlt⟩
        injection he with h1 h2 _
        subst h1 h2
        exact ⟨_, _, _, rfl, hlt⟩

/-- Adding `1` to the argument appends one summand to the argument of `phi`. -/
theorem phi_add_one (k : Nat) {a ξ Y : T} (hξ : Good ξ) (h : phi k a ξ = P 0 Y Z) :
    phi k a (T.add ξ one) = P 0 (T.add Y (P 1 (OGd k a) Z)) Z := by
  by_cases hA : AbsP k a ξ
  · obtain ⟨i, d, b, rfl, hlt⟩ := hA
    rw [phi_eq_abs k a hlt] at h
    injection h with _ h
    rw [add_P, phi_eq_abs k a hlt, ← h, add_assoc'', ← OPowTimes_one, ← OPowTimes_add]
    congr 3
    split
    · rfl
    · rw [add_P]
  · rw [phi_eq_dflt k a ξ hA] at h
    injection h with _ h
    rw [phi_eq_dflt k a _ (fun h' => hA ((absP_add_one_iff hξ).mp h')), coefX_add_one hξ,
      OPowTimes_add, OPowTimes_one, ← add_assoc'', h]

/-! ### The successor case -/

theorem tail_lt_psi {c x G lam : T} (hc : T.isNF1 (P 0 c Z)) (hx : x ∈ T.G1 0 c)
    (hxl : x = T.add G lam) (hlam : Cnt lam) : lam < P 0 c Z := by
  cases lam with
  | Z => exact Z_lt_P' _ _ _
  | P i l lr =>
      have hi := hlam.idx; subst hi
      have hl : l ∈ T.G1 0 c := G1_trans 0 hx l (by rw [hxl, G1_add, G1_P0]; simp)
      exact T.Lt.p_mid _ _ _ _ _ (isNF1_G hc l hl)

theorem takeW_add_all {p : Nat → T → Bool} : ∀ {X : T}, AllW p X → ∀ R : T,
    takeW p (T.add X R) = T.add X (takeW p R)
  | Z, _, _ => rfl
  | P i c b, h, R => by
      rw [add_P, add_P]
      show (if p i c then P i c (takeW p (T.add b R)) else Z) = _
      rw [if_pos h.1, takeW_add_all h.2 R]

theorem logA_unc {d : T} (hu : Unc d) (h0 : d ≠ Z) : logA d = P 0 d Z := by
  rw [logA_of_unc_ne (by rw [hu.uncPart]; exact h0), hu.uncPart, hu.cntPart, oadd_Z_right]

theorem lim_P0 {d : T} (h0 : d ≠ Z) : Lim (P 0 d Z) := by
  unfold Lim
  refine And.intro nofun (fun y hy => ?_)
  cases y with
  | Z => injection hy with _ h; exact h0 h
  | P i c b =>
      rw [add_P] at hy
      injection hy with _ _ h
      have := (add_eq_Z_iff.mp h.symm).2
      cases this

theorem minus1_P0 {d r : T} (h0 : d ≠ Z) : minus1 (P 0 d r) = P 0 d r := minus1_of_ne h0

/-- One step of the iteration of `phi k β'` above a fixed point `ψ₀(Y0)`. -/
theorem phi_step (k : Nat) {β' Y0 σ : T} (hβ : Good β') (hk : k = 0 → β' ≠ Z)
    (hY0 : AllW (bigW (thrA k β')) Y0) (hBY : alphaHead k β' ≤ Y0) (hσ : Good σ)
    (hx : Good (P 0 (T.add Y0 (P 1 (T.add (OGd k β') σ) Z)) Z)) :
    phi k β' (P 0 (T.add Y0 (P 1 (T.add (OGd k β') σ) Z)) Z) =
      P 0 (T.add Y0 (P 1 (T.add (OGd k β') (P 0 (T.add Y0 (P 1 (T.add (OGd k β') σ) Z)) Z)) Z)) Z := by
  generalize hd : T.add Y0 (P 1 (T.add (OGd k β') σ) Z) = d at hx ⊢
  have hnb : bigW (thrA k β') 1 (T.add (OGd k β') σ) = false := by
    cases hb : bigW (thrA k β') 1 (T.add (OGd k β') σ) with
    | false => rfl
    | true =>
        exfalso
        rcases bigW_iff.mp hb with h | ⟨_, h⟩
        · omega
        · rw [exp_OGd hβ (OG_ne_Z hk) hσ.cnt] at h
          unfold thrA at h
          rw [thr_eq k hβ] at h
          exact not_lt_of_le' h ((add_lt_add_left_iff _).mpr (Cnt_lt_Om hσ.cnt))
  have hD : headD k β' d = Y0 := by
    rw [← hd]
    show takeW _ _ = Y0
    rw [takeW_add_all hY0]
    show T.add Y0 (if bigW (thrA k β') 1 (T.add (OGd k β') σ) then _ else Z) = Y0
    rw [hnb]; simp [T.add_Z]
  have hdne : d ≠ Y0 := by
    rw [← hd]; intro e
    have := lt_add_of_ne Y0 (show P 1 (T.add (OGd k β') σ) Z ≠ Z by intro e; cases e)
    rw [e] at this; exact lt_irr _ this
  have hdu : Unc d := by
    rw [← hd]; exact Unc.add (AllW.unc_bigW hY0) ⟨Nat.le_refl 1, trivial⟩
  have hd0 : d ≠ Z := by rw [← hd]; intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun
  rcases hBY with hBY | hBY
  · have hlt : alphaHead k β' < headD k β' d := by rw [hD]; exact hBY
    rw [phi_eq_abs k β' hlt, hD, if_neg hdne, OPowTimes_P k β' 0 d Z (by rw [logA_unc hdu hd0]; trivial),
      logA_unc hdu hd0, OPowTimes_Z]
  · have hnA : ¬ AbsP k β' (P 0 d Z) := by
      rintro ⟨i, d', b', he, hlt⟩
      injection he with _ h2 _
      subst h2
      rw [hD, hBY] at hlt
      exact lt_irr _ hlt
    rw [phi_eq_dflt k β' _ hnA, coefX_of_lim hx (lim_P0 hd0), hBY,
      OPowTimes_P k β' 0 d Z (by rw [logA_unc hdu hd0]; trivial), logA_unc hdu hd0, OPowTimes_Z]

theorem dropOm_add_ne {G : T} (hG : G ≠ Z) (Y : T) : dropOm (T.add G Y) = T.add (dropOm G) Y := by
  cases G with
  | Z => exact absurd rfl hG
  | P i a b =>
      rw [add_P]
      by_cases h : i = 1 ∧ a = Z
      · obtain ⟨rfl, rfl⟩ := h; rfl
      · rw [dropOm_P_ne h, dropOm_P_ne h, add_P]

theorem OGd_succ (k : Nat) {β' : T} (hk : k = 0 → β' ≠ Z) :
    OGd k (T.add β' one) = T.add (OGd k β') Om := by
  unfold OGd
  have hOG : OG k (T.add β' one) = T.add (OG k β') Om := by
    unfold OG
    rw [omegaTimes_add, add_assoc'']
    rfl
  rw [hOG, dropOm_add_ne (OG_ne_Z hk)]

/-- Structure of `phi k β ξ` as seen from a smaller index `α`. -/
theorem phi_struct (k : Nat) {α β ξ : T} (hα : Good α) (hβ : Good β) (hξ : Good ξ) (h : α < β) :
    ∃ Y, phi k β ξ = P 0 Y Z ∧ AllW (bigW (thrA k α)) Y ∧ alphaHead k α < Y := by
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

/-- The approximation property of the shape `P 1 (G ++ x) Z` below `P 1 (G ++ Ω) Z`. -/
theorem shapeG_S {Y0 G : T} : ∀ c'', T.isNF1 (P 0 (T.add Y0 c'') Z) → c'' < P 1 (T.add G Om) Z →
    ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧ c'' < P 1 (T.add G (T.add lam one)) Z := by
  intro c'' hcn hlt
  have hS1 : ∀ y, y < P 1 (T.add G one) Z →
      ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧ y < P 1 (T.add G (T.add lam one)) Z :=
    fun y hy => ⟨Z, good_Z, Z_lt_P' _ _ _, hy⟩
  cases c'' with
  | Z => exact hS1 Z (Z_lt_P' _ _ _)
  | P i x c3 =>
      rcases lt_inv _ _ _ _ _ _ hlt with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
      · exact hS1 _ (T.Lt.p_head _ _ _ _ _ _ h)
      · by_cases hxG : x < G
        · exact hS1 _ (T.Lt.p_mid _ _ _ _ _ (lt_of_lt_of_le' hxG (le_add_right' G one)))
        · obtain ⟨lam, rfl⟩ := between_prefix (le_of_not_lt' hxG) h
          have hlamOm : lam < Om := (add_lt_add_left_iff _).mp h
          have hxmem : T.add G lam ∈ T.G1 0 (T.add Y0 (P 1 (T.add G lam) c3)) := by
            rw [G1_add]; apply List.mem_append_right; rw [G1_P0]; simp
          have hxn := isNF1_of_G1 (isNF1_arg hcn) _ hxmem
          have hlamn := isNF1_of_add_right hxn
          have hlamc : Cnt lam := Cnt_of_lt_Om (isNF1_desc hlamn) hlamOm
          refine ⟨lam, ⟨hlamn, hlamc⟩, tail_lt_psi hcn hxmem rfl hlamc, ?_⟩
          apply T.Lt.p_mid
          exact (add_lt_add_left_iff _).mpr (lt_add_of_ne lam nofun)
      · exact absurd h (not_lt_Z' _)

/-- **Successor index**: iterating `phi k β'` above `ψ₀(Y0)` reaches the next fixed point. -/
theorem phiSucc (k : Nat) {β' Y0 : T} (hβ : Good β') (hk : k = 0 → β' ≠ Z)
    (hY0 : AllW (bigW (thrA k β')) Y0) (hBY : alphaHead k β' < Y0) (hg0 : Good (P 0 Y0 Z)) :
    Cof (P 0 (T.add Y0 (P 1 (T.add (OGd k β') Om) Z)) Z)
      (iterT (fun x => phi k β' (minus1 x)) (T.add (P 0 Y0 Z) one)) := by
  have hY0ne : Y0 ≠ Z := fun e => by rw [e] at hBY; exact not_lt_Z' _ hBY
  have ht1 : iterT (fun x => phi k β' (minus1 x)) (T.add (P 0 Y0 Z) one) 1 =
      P 0 (T.add Y0 (P 1 (T.add (OGd k β') Z) Z)) Z := by
    show phi k β' (minus1 (P 0 Y0 one)) = _
    have hD : headD k β' Y0 = Y0 := takeW_of_all _ _ hY0
    rw [minus1_P0 hY0ne, phi_eq_abs k β' (show alphaHead k β' < headD k β' Y0 by rw [hD]; exact hBY),
      hD, if_pos rfl, OPowTimes_one, T.add_Z]
  refine iter_cof Good 1 shapeG_S (fun _ _ h => T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr h))
    (fun x hx => good_phi k β' _ hβ (good_minus1 hx) hk) (good_add_one hg0) (fun σ hσ hx => ?_)
    (fun _ hx => hx) good_Z ht1 (by rw [ht1]; exact Z_lt_P' _ _ _) (fun j hj => ?_)
  · show phi k β' (minus1 _) = _
    rw [minus1_P0 (fun e => hY0ne (add_eq_Z_iff.mp e).1), phi_step k hβ hk hY0 (Or.inl hBY) hσ hx]
  · obtain rfl : j = 0 := by omega
    show P 0 Y0 one < _
    rw [ht1]
    exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_ne _ nofun)

theorem allW_alphaHead (k : Nat) {β' : T} (hβ : Good β') : AllW (bigW (thrA k β')) (alphaHead k β') := by
  cases β' with
  | Z => trivial
  | P j d b =>
      rw [alphaHead_P]
      exact AllW.imp (fun i c hp => predA_to_bigW k hβ hp) (takeW_all _ d)

/-- **Successor index, from `1`**. -/
theorem phiSuccZ (k : Nat) {β' : T} (hβ : Good β') (hk : k = 0 → β' ≠ Z) :
    Cof (P 0 (T.add (alphaHead k β') (P 1 (T.add (OGd k β') Om) Z)) Z)
      (iterT (fun x => phi k β' (minus1 x)) one) := by
  generalize hB : alphaHead k β' = B
  have hBall : AllW (bigW (thrA k β')) B := hB ▸ allW_alphaHead k hβ
  have hBu : Unc B := AllW.unc_bigW hBall
  have hFg : ∀ x, Good x → Good (phi k β' (minus1 x)) :=
    fun x hx => good_phi k β' _ hβ (good_minus1 hx) hk
  have hgood := good_iterT hFg good_one
  have ht1 : iterT (fun x => phi k β' (minus1 x)) one 1 =
      P 0 (T.add B (OPowTimes k β' (coefX k β' Z))) Z := by
    show phi k β' Z = _
    rw [phi_eq_dflt k β' Z (by rintro ⟨_, _, _, h, _⟩; cases h), hB]
  have hY1 : T.add B (OPowTimes k β' (coefX k β' Z)) ≠ Z := by
    intro e
    have he := add_eq_Z_iff.mp e
    cases hp : pureB k β'
    · exact coefX_ne_Z (Or.inr hp) (by
        cases hX : coefX k β' Z with
        | Z => rfl
        | P _ _ _ => rw [hX] at he; exact absurd he.2 (by intro e'; cases e'))
    · rw [← hB] at he; exact (pureB_true hp).1 he.1
  have ht2 : iterT (fun x => phi k β' (minus1 x)) one 2 = P 0 (T.add B (P 1 (T.add (OGd k β')
      (iterT (fun x => phi k β' (minus1 x)) one 1)) Z)) Z := by
    have hg1 := hgood 1
    show phi k β' (minus1 (iterT _ one 1)) = _
    rw [ht1] at hg1 ⊢
    rw [minus1_P0 hY1]
    cases hp : pureB k β'
    · have hc : coefX k β' Z = one := by simp [coefX, hp]; rfl
      rw [hc, OPowTimes_one] at hg1 ⊢
      have := phi_step k hβ hk hBall (Or.inr hB) good_Z (by rwa [T.add_Z])
      rw [T.add_Z] at this
      rw [this]
    · have hc : coefX k β' Z = Z := by simp [coefX, hp]
      rw [hc, OPowTimes_Z, T.add_Z] at hg1 ⊢
      have hB0 : B ≠ Z := by rw [← hB]; exact (pureB_true hp).1
      have hnA : ¬ AbsP k β' (P 0 B Z) := by
        rintro ⟨i, d, b, he, hlt⟩
        injection he with _ h2 _
        subst h2
        rw [show headD k β' B = B from takeW_of_all _ _ hBall, hB] at hlt; exact lt_irr _ hlt
      rw [phi_eq_dflt k β' _ hnA, coefX_of_lim hg1 (lim_P0 hB0), hB,
        OPowTimes_P k β' 0 B Z (by rw [logA_unc hBu hB0]; trivial), logA_unc hBu hB0, OPowTimes_Z]
  have h1 : iterT (fun x => phi k β' (minus1 x)) one 1 <
      iterT (fun x => phi k β' (minus1 x)) one 2 := by
    rw [ht2]
    conv => lhs; rw [ht1]
    apply T.Lt.p_mid
    apply (add_lt_add_left_iff _).mpr
    cases hp : pureB k β'
    · have hc : coefX k β' Z = one := by simp [coefX, hp]; rfl
      rw [hc, OPowTimes_one]
      apply T.Lt.p_mid
      conv => lhs; rw [← T.add_Z (OGd k β')]
      apply (add_lt_add_left_iff _).mpr
      rw [ht1]; exact Z_lt_P' _ _ _
    · have hc : coefX k β' Z = Z := by simp [coefX, hp]
      rw [hc, OPowTimes_Z]
      exact Z_lt_P' _ _ _
  refine iter_cof Good 2 shapeG_S (fun _ _ h => T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr h))
    hFg good_one (fun σ hσ hx => ?_) (fun _ hx => hx) (hgood 1) ht2 h1 (fun j hj => ?_)
  · show phi k β' (minus1 _) = _
    rw [minus1_P0 (fun e => absurd (add_eq_Z_iff.mp e).2 (by intro e; cases e)),
      phi_step k hβ hk hBall (Or.inr hB) hσ hx]
  · match j, hj with
    | 0, _ =>
        rw [show iterT (fun x => phi k β' (minus1 x)) one (0 + 1) = _ from ht1]
        show P 0 Z Z < _
        apply T.Lt.p_mid
        cases hE : T.add B (OPowTimes k β' (coefX k β' Z)) with
        | Z => exact absurd hE hY1
        | P _ _ _ => exact Z_lt_P' _ _ _
    | 1, _ => exact h1

/-!
## Limits of the iterations of the hyperation: successor exponents

For `λ = ω^e` with `e` a successor, `E λ (X + 1)` is the limit of the values
`E δ (E λ X + 1)` for `δ < λ`: iterating the step `E (ω^d)` (`e = d + 1`)
from `E λ X + 1` climbs to the next fixed point.
-/

/-- Countable normal forms below `ξ`. -/
def Below (ξ : T) : Type := {y : T // Good y ∧ y < ξ}

theorem cof_mono {x : T} {ι κ : Type} {s : ι → T} {t : κ → T} (h : Cof x s)
    (hst : ∀ i, ∃ j, s i ≤ t j) : Cof x t := by
  intro b hb hlt
  obtain ⟨i, hi⟩ := h b hb hlt
  obtain ⟨j, hj⟩ := hst i
  exact ⟨j, le_tr hi hj⟩

theorem E_rep0 (n : Nat) (x y : T) : ∀ j, E n (rep0 x j) y = iterT (Eom n (logA x)) y j
  | 0 => by rw [show rep0 x 0 = Z from rfl, E_Z]; rfl
  | j + 1 => by
      show E n (P 0 x (rep0 x j)) y = Eom n (logA x) (iterT (Eom n (logA x)) y j)
      rw [E_P, E_rep0 n x y j]

theorem good_P0_omegaArg {d : T} (hd : Good d) : Good (P 0 (omegaArg d) Z) := by
  rw [← omegaPow_eq]; exact good_omegaPow hd

theorem rep0_lt_omegaPow_succ {d : T} (hd : Good d) :
    ∀ j, rep0 (omegaArg d) j < omegaPow (T.add d one)
  | 0 => by rw [omegaPow_eq]; exact Z_lt_P' _ _ _
  | j + 1 => by
      show P 0 (omegaArg d) (rep0 (omegaArg d) j) < _
      rw [omegaPow_eq]
      apply T.Lt.p_mid
      exact omegaArg_lt hd (good_add_one hd) (lt_add_of_ne _ nofun)

theorem iterT_congr (F G : T → T) (Pr : T → Prop) (x0 : T) (h0 : Pr x0)
    (hP : ∀ x, Pr x → Pr (F x)) (hFG : ∀ x, Pr x → F x = G x) :
    ∀ j, Pr (iterT F x0 j) ∧ iterT F x0 j = iterT G x0 j
  | 0 => ⟨h0, rfl⟩
  | j + 1 => by
      obtain ⟨h1, h2⟩ := iterT_congr F G Pr x0 h0 hP hFG j
      refine ⟨hP _ h1, ?_⟩
      show F (iterT F x0 j) = G (iterT G x0 j)
      rw [hFG _ h1, h2]

/-- The statement of the fixed-point limit for the exponent `e` at level `n + 1`. -/
def FLStmt (n : Nat) (e X : T) : Prop :=
  Cof (Eom (n + 1) e (T.add X one))
    (fun δ : Below (omegaPow e) => E (n + 1) δ.1 (T.add (Eom (n + 1) e X) one))

theorem fl_of_iter (n : Nat) {d X : T} (hd : Good d)
    (h : Cof (Eom (n + 1) (T.add d one) (T.add X one))
      (iterT (Eom (n + 1) d) (T.add (Eom (n + 1) (T.add d one) X) one))) :
    FLStmt n (T.add d one) X := by
  apply cof_mono h
  intro j
  refine ⟨⟨rep0 (omegaArg d) j, good_rep0 (good_P0_omegaArg hd) j, rep0_lt_omegaPow_succ hd j⟩, ?_⟩
  show _ ≤ E (n + 1) (rep0 (omegaArg d) j) _
  rw [E_rep0, logA_omegaArg hd]
  exact le_refl' _

theorem minus1_add_one {X : T} (hX : X ≠ Z) : minus1 (T.add X one) = T.add (minus1 X) one := by
  cases X with
  | Z => exact absurd rfl hX
  | P i a b =>
      rw [add_P]
      cases i with
      | zero =>
          cases a with
          | Z => rfl
          | P _ _ _ => rfl
      | succ i => rfl

theorem o_single_one : ∀ n, o n [one] = P 0 one Z
  | 0 => by rw [o_single_zero]; rfl
  | n + 1 => by rw [o_single, E_one, Eom_succ_Z, o_single_one n]; rfl

theorem add_one_ne_Z (X : T) : T.add X one ≠ Z := by
  intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun

theorem cnt_lt_psi_add {Y0 σ : T} (h : T.isNF1 (P 0 (T.add Y0 σ) Z)) (hσ : Cnt σ) :
    σ < P 0 (T.add Y0 σ) Z := by
  cases σ with
  | Z => exact Z_lt_P' _ _ _
  | P i l r =>
      have hi := hσ.idx; subst hi
      apply T.Lt.p_mid
      apply isNF1_G h l
      rw [G1_add]; apply List.mem_append_right; rw [G1_P0]; simp

/-! ### Level `1`: the `ε`-iteration -/

theorem Eom1Z (y : T) : Eom 1 Z y = minus1 (omegaPow y) := by
  rw [Eom_succ_Z, o_single_zero]

theorem epsStep {Y0 σ : T} (hY0 : Unc Y0) (hσ : Cnt σ) (hσ0 : σ ≠ Z) :
    Eom 1 Z (P 0 (T.add Y0 σ) Z) = P 0 (T.add Y0 (P 0 (T.add Y0 σ) Z)) Z := by
  rw [Eom1Z]
  have hu : uncPart (T.add Y0 σ) = Y0 := by
    rw [uncPart_add_unc hY0]
    cases σ with
    | Z => exact absurd rfl hσ0
    | P i a b => have hi := hσ.idx; subst hi; exact T.add_Z Y0
  have hc : cntPart (T.add Y0 σ) = σ := by
    rw [cntPart_add_unc hY0]
    cases σ with
    | Z => exact absurd rfl hσ0
    | P i a b => have hi := hσ.idx; subst hi; rfl
  have hω : omegaPow (P 0 (T.add Y0 σ) Z) = P 0 (T.add Y0 (P 0 (T.add Y0 σ) Z)) Z := by
    show (if uncPart (T.add Y0 σ) = Z then _ else if cntPart (T.add Y0 σ) = Z then _ else _) = _
    rw [hu, hc]
    by_cases hY : Y0 = Z
    · subst hY; rw [if_pos rfl]; rfl
    · rw [if_neg hY, if_neg hσ0]
  rw [hω, minus1_P0 (by intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun)]

/-- The `ε`-iteration from `ψ₀(Y0 + 1)` reaches `ψ₀(Y0 + Ω)`. -/
theorem epsIter {Y0 x0 : T} (hY0 : Unc Y0) (hx0 : Good x0)
    (ht1 : iterT (Eom 1 Z) x0 1 = P 0 (T.add Y0 one) Z) (h01 : x0 < iterT (Eom 1 Z) x0 1) :
    Cof (P 0 (T.add Y0 Om) Z) (iterT (Eom 1 Z) x0) := by
  refine iter_cof (S := fun x => x) (σ0 := one) (fun σ => Cnt σ ∧ σ ≠ Z) 1 (fun c'' hcn hlt => ?_)
    (fun _ _ h => h) (fun _ h => Eom_good (facts 0) good_Z h) hx0
    (fun σ hσ _ => epsStep hY0 hσ.1 hσ.2) (fun _ hx => ⟨hx.cnt, by intro e; cases e⟩)
    ⟨⟨rfl, trivial⟩, by intro e; cases e⟩ ht1
    (by rw [ht1]; exact T.Lt.p_mid _ _ _ _ _ (lt_of_le_of_lt' (Z_le' Y0)
      (lt_add_of_ne Y0 nofun))) (fun j hj => ?_)
  · have hn := isNF1_of_add_right (isNF1_arg hcn)
    have hc : Cnt c'' := Cnt_of_lt_Om (isNF1_desc hn) hlt
    exact ⟨c'', ⟨hn, hc⟩, cnt_lt_psi_add hcn hc, lt_add_of_ne _ nofun⟩
  · obtain rfl : j = 0 := by omega
    exact h01

theorem phi_zero_one_Z : phi 0 one Z = P 0 Om Z := rfl

theorem OGd_zero_one : OGd 0 one = Z := rfl

/-- **Level `1`, exponent `1`**. -/
theorem flEps {X : T} (hX : Good X) : FLStmt 0 one X := by
  apply fl_of_iter 0 good_Z
  show Cof (Eom 1 one (T.add X one)) (iterT (Eom 1 Z) (T.add (Eom 1 one X) one))
  have hone : one ≠ Z := by intro e; cases e
  by_cases hX0 : X = Z
  · subst hX0
    have h0 : Eom 1 one Z = Z := Eom_succ_Zarg 0 one
    have htop : Eom 1 one (T.add Z one) = P 0 (T.add Z Om) Z := by
      show Eom 1 one one = _
      rw [Eom_succ_ne 0 hone, if_neg hone]
      exact phi_zero_one_Z
    rw [htop]
    apply epsIter (Y0 := Z) trivial (good_add_one (Eom_good (facts 0) good_one good_Z))
    · show Eom 1 Z (T.add (Eom 1 one Z) one) = _
      rw [h0, Eom1Z]; rfl
    · show T.add (Eom 1 one Z) one < Eom 1 Z (T.add (Eom 1 one Z) one)
      rw [h0, Eom1Z]
      exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
  · have hΦ : Eom 1 one X = phi 0 one (minus1 X) := by
      rw [Eom_succ_ne 0 hone, if_neg hX0]; rfl
    obtain ⟨Y0, hY0e, hY0ne, hY0b⟩ := phi_lvl 0 one (minus1 X) good_one (good_minus1 hX)
    have hu := hY0b.unc
    have htop : Eom 1 one (T.add X one) = P 0 (T.add Y0 Om) Z := by
      rw [Eom_succ_ne 0 hone, if_neg (add_one_ne_Z X)]
      show phi 0 one (minus1 (T.add X one)) = _
      rw [minus1_add_one hX0, phi_add_one 0 (good_minus1 hX) hY0e, OGd_zero_one]
      rfl
    rw [htop]
    have ht0 : T.add (Eom 1 one X) one = P 0 Y0 one := by rw [hΦ, hY0e, add_P]; rfl
    have ht1 : Eom 1 Z (P 0 Y0 one) = P 0 (T.add Y0 one) Z := by
      rw [Eom1Z]
      have hω : omegaPow (P 0 Y0 one) = P 0 (T.add Y0 one) Z := by
        show (if uncPart Y0 = Z then _ else if cntPart Y0 = Z then _ else _) = _
        rw [hu.uncPart, if_neg hY0ne, if_pos hu.cntPart]
      rw [hω, minus1_P0 (add_one_ne_Z Y0)]
    apply epsIter hu (good_add_one (Eom_good (facts 0) good_one hX))
    · show Eom 1 Z (T.add (Eom 1 one X) one) = _
      rw [ht0, ht1]
    · show T.add (Eom 1 one X) one < Eom 1 Z (T.add (Eom 1 one X) one)
      rw [ht0, ht1]
      exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_ne _ nofun)

/-! ### Levels `≥ 2`: the `Γ`-iteration -/

theorem dropOm_copies_add (n : Nat) {y r : T} (hy : y ≠ Z) :
    dropOm (T.add (copies Om n) (P 1 y r)) = T.add (copies Om n) (P 1 y r) := by
  cases n with
  | zero => exact dropOm_P_ne (fun h => hy h.2)
  | succ n =>
      show dropOm (T.add (P 1 Om (copies Om n)) _) = _
      rw [add_P]
      exact dropOm_P_ne (fun h => by cases h.2)

theorem copies_succ_eq (n : Nat) : copies Om (n + 1) = T.add (copies Om n) (P 1 Om Z) := by
  rw [copies_add Om n 1]; rfl

theorem predA_false_of_lt {n : Nat} {G : T} (h : G < copies Om (n + 1)) : predA n 1 G = false := by
  cases hp : predA n 1 G with
  | false => rfl
  | true =>
      exfalso
      rcases predA_iff.mp hp with h' | ⟨_, h'⟩
      · omega
      · exact not_lt_of_le' h' h

theorem EomZ_succ (n : Nat) (y : T) : Eom (n + 2) Z y = minus1 (E (n + 1) y one) := by
  rw [Eom_succ_Z, o_single]

theorem OGd_succ_Z (n : Nat) : OGd (n + 1) Z = copies Om (n + 1) := by
  show dropOm (T.add (copies Om (n + 1)) Z) = _
  rw [T.add_Z]; rfl

theorem phi_succ_Z_Z (n : Nat) : phi (n + 1) Z Z = P 0 (P 1 (copies Om (n + 1)) Z) Z := by
  rw [phi_eq_dflt _ _ Z (by rintro ⟨_, _, _, h, _⟩; cases h)]
  have hp : pureB (n + 1) Z = false := rfl
  rw [show coefX (n + 1) Z Z = one by simp [coefX, hp]; rfl, OPowTimes_one, OGd_succ_Z]
  rfl

/-- One step of the `Γ`-iteration. -/
theorem gammaStep (n : Nat) {Y0 G1 : T} (hY0 : AllBigK (n + 1) Y0) (hG1 : G1 < copies Om (n + 1)) :
    Eom (n + 2) Z (P 0 (T.add Y0 (P 1 G1 Z)) Z) =
      P 0 (T.add Y0 (P 1 (T.add (copies Om n) (P 1 (P 0 (T.add Y0 (P 1 G1 Z)) Z) Z)) Z)) Z := by
  generalize hc : T.add Y0 (P 1 G1 Z) = c
  have hcu : Unc c := by rw [← hc]; exact Unc.add hY0.unc ⟨Nat.le_refl 1, trivial⟩
  have hc0 : c ≠ Z := by
    rw [← hc]; intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun
  have hcY : c ≠ Y0 := by
    rw [← hc]; intro e
    have := lt_add_of_ne Y0 (show P 1 G1 Z ≠ Z by intro e; cases e)
    rw [e] at this; exact lt_irr _ this
  have ht0 : P 0 c Z ≠ Z := by intro e; cases e
  rw [EomZ_succ, E_P, E_Z, logA_unc hcu hc0, Eom_succ_ne n ht0, if_neg nofun]
  have hm : (if n = 0 then P 0 c Z else minus1 (P 0 c Z)) = P 0 c Z := by
    split
    · rfl
    · exact minus1_P0 hc0
  rw [hm, show minus1 one = Z from rfl, phi_eq_dflt n _ Z (by rintro ⟨_, _, _, h, _⟩; cases h)]
  have hB : alphaHead n (P 0 c Z) = Y0 := by
    rw [alphaHead_P, ← hc, takeW_add_all hY0.allW_predA]
    show T.add Y0 (if predA n 1 G1 then _ else Z) = Y0
    rw [predA_false_of_lt hG1]; exact T.add_Z Y0
  have hp : pureB n (P 0 c Z) = false := by
    unfold pureB; rw [hB]
    have : decide (P 0 c Z = P 0 Y0 Z) = false :=
      decide_eq_false (fun e => by injection e with _ h _; exact hcY h)
    rw [this, Bool.and_false]
  have hcoef : coefX n (P 0 c Z) Z = one := by simp [coefX, hp]; rfl
  have hOGd : OGd n (P 0 c Z) = T.add (copies Om n) (P 1 (P 0 c Z) Z) := by
    show dropOm (T.add (copies Om n) (P 1 (logA c) (omegaTimes Z))) = _
    rw [logA_unc hcu hc0]
    exact dropOm_copies_add n ht0
  rw [hcoef, OPowTimes_one, hB, hOGd]
  exact minus1_P0 (by intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun)

theorem shapeGam_S {Y0 G : T} : ∀ c'', T.isNF1 (P 0 (T.add Y0 c'') Z) →
    c'' < P 1 (T.add G (P 1 Om Z)) Z →
    ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧
      c'' < P 1 (T.add G (P 1 (T.add lam one) Z)) Z := by
  intro c'' hcn hlt
  have hS1 : ∀ y, y < P 1 (T.add G (P 1 one Z)) Z →
      ∃ lam, Good lam ∧ lam < P 0 (T.add Y0 c'') Z ∧ y < P 1 (T.add G (P 1 (T.add lam one) Z)) Z :=
    fun y hy => ⟨Z, good_Z, Z_lt_P' _ _ _, hy⟩
  cases c'' with
  | Z => exact hS1 Z (Z_lt_P' _ _ _)
  | P i x c3 =>
      rcases lt_inv _ _ _ _ _ _ hlt with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
      · exact hS1 _ (T.Lt.p_head _ _ _ _ _ _ h)
      · by_cases hxG : x < G
        · exact hS1 _ (T.Lt.p_mid _ _ _ _ _ (lt_of_lt_of_le' hxG (le_add_right' G _)))
        · obtain ⟨y, rfl⟩ := between_prefix (le_of_not_lt' hxG) h
          have hy : y < P 1 Om Z := (add_lt_add_left_iff _).mp h
          cases y with
          | Z =>
              apply hS1
              apply T.Lt.p_mid
              rw [T.add_Z]
              exact lt_add_of_ne _ nofun
          | P j u y3 =>
              rcases lt_inv _ _ _ _ _ _ hy with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
              · exact hS1 _ (T.Lt.p_mid _ _ _ _ _
                  ((add_lt_add_left_iff _).mpr (T.Lt.p_head _ _ _ _ _ _ h2)))
              · have hmem : u ∈ T.G1 0 (T.add Y0 (P 1 (T.add G (P 1 u y3)) c3)) := by
                  simp [G1_add, G1_P0]
                have hun := isNF1_of_G1 (isNF1_arg hcn) _ hmem
                have huc : Cnt u := Cnt_of_lt_Om (isNF1_desc hun) h2
                refine ⟨u, ⟨hun, huc⟩, lt_psi_of_comp hcn u hmem huc, ?_⟩
                apply T.Lt.p_mid; apply (add_lt_add_left_iff _).mpr; apply T.Lt.p_mid
                exact lt_add_of_ne u nofun
              · exact absurd h2 (not_lt_Z' _)
      · exact absurd h (not_lt_Z' _)

/-- The `Γ`-iteration from `ψ₀(Y0 + ψ₁(G1))` reaches `ψ₀(Y0 + ψ₁(Ω·(n+1)))`. -/
theorem gammaIter (n : Nat) {Y0 G1 x0 : T} (j0 : Nat) (hY0 : AllBigK (n + 1) Y0)
    (hG1 : G1 < copies Om (n + 1)) (hx0 : Good x0)
    (ht0 : iterT (Eom (n + 2) Z) x0 j0 = P 0 (T.add Y0 (P 1 G1 Z)) Z)
    (hG01 : G1 < T.add (copies Om n) (P 1 (iterT (Eom (n + 2) Z) x0 j0) Z))
    (hpre : ∀ j, j < j0 → iterT (Eom (n + 2) Z) x0 j < iterT (Eom (n + 2) Z) x0 (j + 1)) :
    Cof (P 0 (T.add Y0 (P 1 (copies Om (n + 1)) Z)) Z) (iterT (Eom (n + 2) Z) x0) := by
  have hF : ∀ x, Good x → Good (Eom (n + 2) Z x) := fun _ h => Eom_good (facts (n + 1)) good_Z h
  have ht1 : iterT (Eom (n + 2) Z) x0 (j0 + 1) = P 0 (T.add Y0 (P 1 (T.add (copies Om n)
      (P 1 (iterT (Eom (n + 2) Z) x0 j0) Z)) Z)) Z := by
    show Eom (n + 2) Z _ = _
    conv => lhs; rw [ht0]
    rw [gammaStep n hY0 hG1, ← ht0]
  have hlt : iterT (Eom (n + 2) Z) x0 j0 < iterT (Eom (n + 2) Z) x0 (j0 + 1) := by
    rw [ht1]
    conv => lhs; rw [ht0]
    exact T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr (T.Lt.p_mid _ _ _ _ _ hG01))
  rw [copies_succ_eq]
  refine iter_cof (S := fun x => P 1 (T.add (copies Om n) (P 1 x Z)) Z) Cnt (j0 + 1) shapeGam_S
    (fun _ _ h => T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr (T.Lt.p_mid _ _ _ _ _ h))) hF hx0
    (fun σ hσ _ => gammaStep n hY0 (by
      rw [copies_succ_eq]
      exact (add_lt_add_left_iff _).mpr (T.Lt.p_mid _ _ _ _ _ (Cnt_lt_Om hσ))))
    (fun _ hx => hx.cnt) (good_iterT hF hx0 j0).cnt ht1 hlt (fun j hj => ?_)
  rcases Nat.lt_or_ge j j0 with h | h
  · exact hpre j h
  · obtain rfl : j = j0 := by omega
    exact hlt

theorem phi_n_one_Z (n : Nat) :
    phi n (if n = 0 then one else Z) Z = P 0 (P 1 (copies Om n) Z) Z := by
  cases n with
  | zero => rfl
  | succ n => rw [if_neg (Nat.succ_ne_zero n)]; exact phi_succ_Z_Z n

/-- **Levels `≥ 2`, exponent `1`**. -/
theorem flGamma (n : Nat) {X : T} (hX : Good X) : FLStmt (n + 1) one X := by
  apply fl_of_iter (n + 1) good_Z
  show Cof (Eom (n + 2) one (T.add X one)) (iterT (Eom (n + 2) Z) (T.add (Eom (n + 2) one X) one))
  have hone : one ≠ Z := by intro e; cases e
  have hEone : E (n + 1) one one = P 0 one Z := by
    rw [E_one, Eom_succ_Z, o_single_one]; rfl
  by_cases hX0 : X = Z
  · subst hX0
    have h0 : Eom (n + 2) one Z = Z := Eom_succ_Zarg (n + 1) one
    have htop : Eom (n + 2) one (T.add Z one) = P 0 (T.add Z (P 1 (copies Om (n + 1)) Z)) Z := by
      show Eom (n + 2) one one = _
      rw [Eom_succ_ne (n + 1) hone, if_neg hone, if_neg (Nat.succ_ne_zero n)]
      exact phi_succ_Z_Z n
    rw [htop]
    have ht1 : iterT (Eom (n + 2) Z) (T.add (Eom (n + 2) one Z) one) 1 = P 0 one Z := by
      show Eom (n + 2) Z (T.add (Eom (n + 2) one Z) one) = _
      rw [h0, show T.add Z one = one from rfl, EomZ_succ, hEone]; rfl
    have ht2 : iterT (Eom (n + 2) Z) (T.add (Eom (n + 2) one Z) one) 2 =
        P 0 (T.add Z (P 1 (copies Om n) Z)) Z := by
      show Eom (n + 2) Z (iterT (Eom (n + 2) Z) (T.add (Eom (n + 2) one Z) one) 1) = _
      rw [ht1, EomZ_succ, E_P, E_Z, show logA one = one from rfl,
        Eom_succ_ne n hone, if_neg hone, show minus1 one = Z from rfl, phi_n_one_Z]
      exact minus1_P0 nofun
    have hG1 : copies Om n < copies Om (n + 1) := by
      rw [copies_succ_eq]; exact lt_add_of_ne _ nofun
    apply gammaIter n 2 (Y0 := Z) trivial hG1 (good_add_one (Eom_good (facts (n + 1)) good_one good_Z)) ht2
      (lt_add_of_ne _ nofun)
    intro j hj
    match j, hj with
    | 0, _ =>
        show T.add (Eom (n + 2) one Z) one < _
        rw [ht1, h0]
        exact T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
    | 1, _ =>
        rw [ht1, ht2]
        exact T.Lt.p_mid _ _ _ _ _ (T.Lt.p_head _ _ _ _ _ _ (by omega))
  · have hΦ : Eom (n + 2) one X = phi (n + 1) Z (minus1 X) := by
      rw [Eom_succ_ne (n + 1) hone, if_neg hX0, if_neg (Nat.succ_ne_zero n)]; rfl
    obtain ⟨Y0, hY0e, hY0ne, hY0b⟩ := phi_lvl (n + 1) Z (minus1 X) good_Z (good_minus1 hX)
    have hLvl : Lvl (n + 1) (P 0 Y0 Z) := ⟨Y0, rfl, hY0ne, hY0b⟩
    have htop : Eom (n + 2) one (T.add X one) = P 0 (T.add Y0 (P 1 (copies Om (n + 1)) Z)) Z := by
      rw [Eom_succ_ne (n + 1) hone, if_neg (add_one_ne_Z X), if_neg (Nat.succ_ne_zero n)]
      show phi (n + 1) Z (minus1 (T.add X one)) = _
      rw [minus1_add_one hX0, phi_add_one (n + 1) (good_minus1 hX) hY0e, OGd_succ_Z]
    rw [htop]
    have ht0 : T.add (Eom (n + 2) one X) one = P 0 Y0 one := by rw [hΦ, hY0e, add_P]; rfl
    have ht1 : iterT (Eom (n + 2) Z) (T.add (Eom (n + 2) one X) one) 1 =
        P 0 (T.add Y0 (P 1 (T.add (copies Om n) (P 1 (P 0 Y0 Z) one)) Z)) Z := by
      show Eom (n + 2) Z (T.add (Eom (n + 2) one X) one) = _
      rw [ht0, EomZ_succ, E_P, hEone, hLvl.logA, Eom_succ_ne n hLvl.ne_Z,
        if_neg nofun]
      have hm : (if n = 0 then P 0 Y0 Z else minus1 (P 0 Y0 Z)) = P 0 Y0 Z := by
        split
        · rfl
        · exact hLvl.minus1
      rw [hm, show minus1 (P 0 one Z) = P 0 one Z from rfl]
      have hD : headD n (P 0 Y0 Z) one = Z := rfl
      have hnA : ¬ AbsP n (P 0 Y0 Z) (P 0 one Z) := by
        rintro ⟨i, d, b, he, hlt⟩
        injection he with _ h2 _
        subst h2
        rw [hD] at hlt
        exact not_lt_Z' _ hlt
      have hB : alphaHead n (P 0 Y0 Z) = Y0 := by
        rw [alphaHead_P]; exact takeW_of_all _ _ hY0b.allW_predA
      have hp : pureB n (P 0 Y0 Z) = true := by simp [pureB, hB, hY0ne]
      have hOG : T.add (OGd n (P 0 Y0 Z)) (logA one) = T.add (copies Om n) (P 1 (P 0 Y0 Z) one) := by
        show T.add (dropOm (T.add (copies Om n) (P 1 (logA Y0) (omegaTimes Z)))) one = _
        rw [hLvl.logA, show omegaTimes Z = Z from rfl, dropOm_copies_add n hLvl.ne_Z, add_assoc'',
          add_P]
        rfl
      rw [phi_eq_dflt _ _ _ hnA, hB, show coefX n (P 0 Y0 Z) (P 0 one Z) = P 0 one Z by simp [coefX, hp],
        OPowTimes_P n _ 0 one Z ⟨rfl, trivial⟩, hOG, OPowTimes_Z]
      exact minus1_P0 (by intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun)
    have hG1 : T.add (copies Om n) (P 1 (P 0 Y0 Z) one) < copies Om (n + 1) := by
      rw [copies_succ_eq]
      exact (add_lt_add_left_iff _).mpr (T.Lt.p_mid _ _ _ _ _ (T.Lt.p_head _ _ _ _ _ _ (by omega)))
    apply gammaIter n 1 hY0b hG1 (good_add_one (Eom_good (facts (n + 1)) good_one hX)) ht1
    · apply (add_lt_add_left_iff _).mpr
      apply T.Lt.p_mid
      rw [ht1]
      exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_ne _ nofun)
    · intro j hj
      match j, hj with
      | 0, _ =>
          show T.add (Eom (n + 2) one X) one < _
          rw [ht1, ht0]
          exact T.Lt.p_mid _ _ _ _ _ (lt_add_of_ne _ nofun)

/-! ### Successor exponents `d + 1` with `d ≠ 0` -/

theorem alphaHead_add_one (k : Nat) (a : T) : alphaHead k (T.add a one) = alphaHead k a := by
  cases a with
  | Z => rfl
  | P j d b => rw [add_P]; rfl

theorem pureB_add_one (k : Nat) (a : T) : pureB k (T.add a one) = false := by
  unfold pureB
  cases a with
  | Z =>
      have : decide (alphaHead k (T.add Z one) ≠ Z) = false :=
        decide_eq_false (fun h => h rfl)
      rw [this, Bool.false_and]
  | P j c b =>
      have : decide (T.add (P j c b) one = P 0 (alphaHead k (T.add (P j c b) one)) Z) = false :=
        decide_eq_false (fun e => by
          rw [add_P] at e
          injection e with _ _ h
          exact add_one_ne_Z b h)
      rw [this, Bool.and_false]

theorem phi_succ_index_Z (k : Nat) {d' : T} (hk : k = 0 → d' ≠ Z) :
    phi k (T.add d' one) Z = P 0 (T.add (alphaHead k d') (P 1 (T.add (OGd k d') Om) Z)) Z := by
  rw [phi_eq_dflt _ _ Z (by rintro ⟨_, _, _, h, _⟩; cases h), alphaHead_add_one]
  have hc : coefX k (T.add d' one) Z = one := by simp [coefX, pureB_add_one]; rfl
  rw [hc, OPowTimes_one, OGd_succ k hk]

theorem iterT_eq_of {F G : T → T} (Pr : T → Prop) {x0 : T} (h0 : Pr x0)
    (hP : ∀ x, Pr x → Pr (F x)) (hFG : ∀ x, Pr x → F x = G x) :
    iterT F x0 = iterT G x0 := by
  funext j; exact (iterT_congr F G Pr x0 h0 hP hFG j).2

/-- **Successor exponents** `d + 1`, `d ≠ 0`. -/
theorem flSucc (n : Nat) {d X : T} (hd : Good d) (hd0 : d ≠ Z) (hX : Good X) :
    FLStmt n (T.add d one) X := by
  apply fl_of_iter n hd
  generalize hdd : (if n = 0 then d else minus1 d) = d'
  have hd' : Good d' := by
    rw [← hdd]; split
    · exact hd
    · exact good_minus1 hd
  have hk' : n = 0 → d' ≠ Z := by
    intro h; rw [← hdd, if_pos h]; exact hd0
  have he' : (if n = 0 then T.add d one else minus1 (T.add d one)) = T.add d' one := by
    rw [← hdd]; split
    · rfl
    · exact minus1_add_one hd0
  have hEd : ∀ y, y ≠ Z → Eom (n + 1) d y = phi n d' (minus1 y) := by
    intro y hy; rw [Eom_succ_ne n hd0, if_neg hy, hdd]
  have hEe : ∀ y, y ≠ Z → Eom (n + 1) (T.add d one) y = phi n (T.add d' one) (minus1 y) := by
    intro y hy; rw [Eom_succ_ne n (add_one_ne_Z d), if_neg hy, he']
  have hiter : ∀ y0, Good y0 → y0 ≠ Z →
      iterT (Eom (n + 1) d) y0 = iterT (fun x => phi n d' (minus1 x)) y0 := by
    intro y0 hy0 hy00
    apply iterT_eq_of (fun x => Good x ∧ x ≠ Z) ⟨hy0, hy00⟩
    · intro x ⟨hx, hx0⟩
      refine ⟨Eom_good (facts n) hd hx, ?_⟩
      rw [hEd x hx0]
      exact (phi_lvl n d' _ hd' (good_minus1 hx)).ne_Z
    · intro x ⟨_, hx0⟩; exact hEd x hx0
  by_cases hX0 : X = Z
  · subst hX0
    have h0 : Eom (n + 1) (T.add d one) Z = Z := Eom_succ_Zarg n _
    rw [h0, show T.add Z one = one from rfl, hiter _ good_one nofun]
    have htop : Eom (n + 1) (T.add d one) one =
        P 0 (T.add (alphaHead n d') (P 1 (T.add (OGd n d') Om) Z)) Z := by
      rw [hEe _ (by intro e; cases e)]
      exact phi_succ_index_Z n hk'
    rw [htop]
    exact phiSuccZ n hd' hk'
  · obtain ⟨Y, hYe, hYw, hBY⟩ := phi_struct n hd' (good_add_one hd') (good_minus1 hX)
      (lt_add_of_ne d' nofun)
    have hΦ : Eom (n + 1) (T.add d one) X = P 0 Y Z := by rw [hEe X hX0, hYe]
    have hg0 : Good (P 0 Y Z) := by
      rw [← hYe]
      exact good_phi n _ _ (good_add_one hd') (good_minus1 hX) (fun _ => add_one_ne_Z d')
    have htop : Eom (n + 1) (T.add d one) (T.add X one) =
        P 0 (T.add Y (P 1 (T.add (OGd n d') Om) Z)) Z := by
      rw [hEe _ (add_one_ne_Z X), minus1_add_one hX0, phi_add_one n (good_minus1 hX) hYe,
        OGd_succ n hk']
    rw [hΦ, hiter _ (good_add_one hg0) (add_one_ne_Z _), htop]
    exact phiSucc n hd' hk' hYw hBY hg0

theorem good_cases {e : T} (he : Good e) :
    e = Z ∨ (∃ d, Good d ∧ e = T.add d one) ∨ Lim e := by
  induction e with
  | Z => exact Or.inl rfl
  | P i a b _ ihb =>
      have hi := he.idx; subst hi
      cases b with
      | Z =>
          cases a with
          | Z => exact Or.inr (Or.inl ⟨Z, good_Z, rfl⟩)
          | P _ _ _ => exact Or.inr (Or.inr (lim_P0 nofun))
      | P j c r =>
          rcases ihb he.tail with h | ⟨d, hd, hdb⟩ | hl
          · cases h
          · refine Or.inr (Or.inl ⟨P 0 a d, ?_, by rw [hdb, add_P]⟩)
            have hn : T.isNF1 (T.add (P 0 a d) one) := by rw [add_P, ← hdb]; exact he.nf
            exact ⟨isNF1_of_add_left hn, rfl, hd.cnt⟩
          · refine Or.inr (Or.inr ⟨nofun, fun y hy => ?_⟩)
            cases y with
            | Z =>
                change P 0 a (P j c r) = P 0 Z Z at hy
                injection hy with _ _ h
                cases h
            | P i' u v =>
                rw [add_P] at hy
                injection hy with _ _ h
                exact hl.2 v h

/-!
## Limits of the iterations of the hyperation: limit exponents

For `λ = ω^e` with `e` a limit, `E λ (X + 1)` is the limit of `E (ω^d) (E λ X + 1)`
for `d < e`.  Together with the successor case this gives the fixed-point limit
`fl` for every exponent.
-/

/-! ### `Ω·x` and `Ω^(Ω·k + a)` -/

theorem omegaTimes_eq_OPT : ∀ x : T, omegaTimes x = OPowTimes 0 one x
  | Z => rfl
  | P i c b => by
      show P 1 (logA c) (omegaTimes b) = P 1 (dropOm (T.add (OG 0 one) (logA c))) (OPowTimes 0 one b)
      rw [omegaTimes_eq_OPT b, show OG 0 one = P 1 Z Z from rfl, add_P, add_Z_left']
      rfl

theorem oadd_Om_le_add : ∀ {X : T}, Unc X → Desc X → oadd Om X ≤ T.add X Om
  | Z, _, _ => le_refl' _
  | P i c X', hu, hd => by
      by_cases hlt : P 1 Z Z < P i c Z
      · rw [show Om = P 1 Z Z from rfl, oadd_P_of_lt hlt]
        exact le_add_right' _ _
      · have hi : i = 1 := by
          rcases Nat.lt_or_ge 1 i with h1 | h1
          · exact absurd (T.Lt.p_head _ _ _ _ _ _ h1) hlt
          · have := hu.1; omega
        subst hi
        have hc : c = Z := by
          cases c with
          | Z => rfl
          | P _ _ _ => exact absurd (T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)) hlt
        subst hc
        rw [show Om = P 1 Z Z from rfl, oadd_P_of_not_lt hlt, oadd_Z_left, add_P]
        apply P_le_P_tail
        have ih := oadd_Om_le_add hu.2 hd.tail
        have hnl : ¬ P 1 Z Z < T.head X' := not_lt_of_le' hd.hd
        rw [show Om = P 1 Z Z from rfl, oadd_P_of_not_lt hnl, oadd_Z_left] at ih
        exact ih

theorem OG_eq_oadd (k : Nat) {a : T} (ha : Good a) (hk : k = 0 → a ≠ Z) :
    OG k a = oadd Om (OGd k a) := by
  have e1 := exp_OGd (lam := Z) ha (OG_ne_Z hk) trivial
  simp only [T.add_Z] at e1
  exact e1.symm

theorem OG_le_OGd_add (k : Nat) {a : T} (ha : Good a) (hk : k = 0 → a ≠ Z) :
    OG k a ≤ T.add (OGd k a) Om := by
  rw [OG_eq_oadd k ha hk]
  exact oadd_Om_le_add (unc_OGd k a) (isNF1_desc (isNF1_OGd k ha))

theorem OGd_lt (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (hk : k = 0 → α ≠ Z)
    (h : α < β) : OGd k α < OGd k β := by
  have hkβ : k = 0 → β ≠ Z := fun _ e => by subst e; exact not_lt_Z' _ h
  apply lt_of_oadd_Om_lt
  rw [← OG_eq_oadd k hα hk, ← OG_eq_oadd k hβ hkβ]
  exact lt_of_lt_of_le' (lt_add_of_ne _ (by intro e; cases e)) (OG_succ_le k hα hβ h)

theorem OGd_le (k : Nat) {α β : T} (hα : Good α) (hβ : Good β) (hk : k = 0 → α ≠ Z)
    (h : α ≤ β) : OGd k α ≤ OGd k β := by
  rcases h with h | rfl
  · exact Or.inl (OGd_lt k hα hβ hk h)
  · exact le_refl' _

/-! ### Limits -/

theorem lim_head {e : T} (he : Good e) (hl : Lim e) : ∃ c b, e = P 0 c b ∧ c ≠ Z := by
  cases e with
  | Z => exact absurd rfl hl.1
  | P i c b =>
      have hi := he.idx; subst hi
      refine ⟨c, b, rfl, fun hc => ?_⟩
      subst hc
      obtain ⟨y, hy⟩ := finite_of_one_head he ⟨b, rfl⟩
      exact hl.2 y hy

theorem minus1_lim {e : T} (he : Good e) (hl : Lim e) : minus1 e = e := by
  obtain ⟨c, b, rfl, hc⟩ := lim_head he hl
  exact minus1_of_ne hc

theorem logA_ne_Z {c : T} (hc : c ≠ Z) : logA c ≠ Z := by
  by_cases hu : uncPart c = Z
  · rw [logA_of_unc_Z hu]; exact hc
  · exact (ne_of_lt'' (Z_lt_logA hu)).symm

theorem OGd_lim (n : Nat) {e : T} (he : Good e) (hl : Lim e) : OGd n e = OG n e := by
  obtain ⟨c, b, rfl, hc⟩ := lim_head he hl
  show dropOm (T.add (copies Om n) (P 1 (logA c) (omegaTimes b))) =
    T.add (copies Om n) (P 1 (logA c) (omegaTimes b))
  exact dropOm_copies_add n (logA_ne_Z hc)

/-- **Continuity of `OGd`** at limits. -/
theorem OGd_cont (n : Nat) {e : T} (he : Good e) (hl : Lim e) {x : T} (hx : T.isNF1 x)
    (hlt : x < OGd n e) :
    ∃ a, Good a ∧ a < e ∧ (n = 0 → a ≠ Z) ∧ x < OGd n (T.add a one) := by
  rw [OGd_lim n he hl] at hlt
  have hone := hl.one_lt he
  by_cases hxG : x < copies Om n
  · exact ⟨one, good_one, hone, (fun _ h => by cases h),
      lt_of_lt_of_le' hxG (copies_le_OGd n _)⟩
  · obtain ⟨y, rfl⟩ := between_prefix (le_of_not_lt' hxG) hlt
    have hy : y < omegaTimes e := (add_lt_add_left_iff _).mp hlt
    rw [omegaTimes_eq_OPT] at hy
    obtain ⟨X, hX, hXe, hyX⟩ := OPT_cont 0 good_one he hl (isNF1_of_add_right hx) hy
    have hX0 : X ≠ Z := by intro h; rw [h] at hyX; exact not_lt_Z' _ hyX
    refine ⟨X, hX, hXe, fun _ => hX0, ?_⟩
    rw [OGd_succ n (fun _ => hX0)]
    apply lt_of_lt_of_le' _ (OG_le_OGd_add n hX (fun _ => hX0))
    show T.add (copies Om n) y < T.add (copies Om n) (omegaTimes X)
    rw [omegaTimes_eq_OPT]
    exact (add_lt_add_left_iff _).mpr hyX

theorem minus1_le {x : T} (hx : Good x) : minus1 x ≤ x := by
  cases x with
  | Z => exact le_refl' _
  | P i a b =>
      cases i with
      | zero =>
          cases a with
          | Z => exact le_of_lt' (tail_lt_of_desc hx.desc)
          | P _ _ _ => exact le_refl' _
      | succ i => exact le_refl' _

theorem fin_succ : ∀ {b : T}, Good (P 0 Z b) → T.add b one = P 0 Z b
  | Z, _ => rfl
  | P j e' r', h => by
      have hj := h.tail.idx; subst hj
      have he' : e' = Z := by
        rcases P0_le_P0_iff.mp h.desc.hd with h' | h'
        · exact absurd h' (not_lt_Z' _)
        · exact h'
      subst he'
      rw [add_P, fin_succ h.tail]

theorem le_minus1_succ {a : T} (ha : Good a) : a ≤ minus1 (T.add a one) := by
  cases a with
  | Z => exact Z_le' _
  | P i c b =>
      have hi := ha.idx; subst hi
      rw [add_P]
      cases c with
      | Z =>
          show P 0 Z b ≤ T.add b one
          rw [fin_succ ha]; exact le_refl' _
      | P j u v =>
          show P 0 (P j u v) b ≤ P 0 (P j u v) (T.add b one)
          exact P_le_P_tail (le_of_lt' (lt_add_of_ne b nofun))

/-! ### `a ≤ φ_k(a, 0)` -/

theorem phi_index_infl (k : Nat) {a : T} (ha : Good a) (hk : k = 0 → a ≠ Z) : a ≤ phi k a Z := by
  cases a with
  | Z => exact Z_le' _
  | P i h r =>
      have hi := ha.idx; subst hi
      rw [phi_eq_dflt k _ Z (by rintro ⟨_, _, _, e, _⟩; cases e)]
      cases hp : pureB k (P 0 h r)
      · have hc : coefX k (P 0 h r) Z = one := by simp [coefX, hp]; rfl
        rw [hc, OPowTimes_one, alphaHead_P]
        apply Or.inl
        apply T.Lt.p_mid
        have hsplit := takeW_add_dropW (predA k) h
        have hBall : AllW (predA k) (takeW (predA k) h) := takeW_all _ h
        generalize takeW (predA k) h = B at hsplit hBall ⊢
        conv => lhs; rw [← hsplit]
        apply (add_lt_add_left_iff _).mpr
        rcases dropW_head (predA k) h with hR | ⟨i, c, R', hR, hpf⟩
        · rw [hR]; exact Z_lt_P' _ _ _
        · rw [hR]
          rw [hR] at hsplit
          have hnb : ¬ BigK (k + 1) i c := fun hb => by rw [predA_iff.mpr hb] at hpf; cases hpf
          rcases Nat.lt_or_ge i 1 with hi1 | hi1
          · exact T.Lt.p_head _ _ _ _ _ _ hi1
          · have hi : i = 1 := by
              rcases Nat.lt_or_ge i 2 with h2 | h2
              · omega
              · exact absurd (Or.inl h2) hnb
            subst hi
            apply T.Lt.p_mid
            have hc1 : c < copies Om (k + 1) := by
              rcases lt_total_thm c (copies Om (k + 1)) with h' | h' | h'
              · exact h'
              · exact absurd (Or.inr ⟨Nat.le_refl 1, Or.inl h'⟩) hnb
              · exact absurd (Or.inr ⟨Nat.le_refl 1, Or.inr h'.symm⟩) hnb
            have hBu : Unc B := AllW.unc_predA hBall
            have hU : uncPart h ≠ Z := by
              rw [← hsplit, uncPart_add_unc hBu]
              intro e; exact absurd (add_eq_Z_iff.mp e).2 nofun
            have hOGd : OGd k (P 0 h r) = T.add (copies Om k) (P 1 (logA h) (omegaTimes r)) := by
              show dropOm (T.add (copies Om k) (P 1 (logA h) (omegaTimes r))) = _
              exact dropOm_copies_add k (ne_of_lt'' (Z_lt_logA hU)).symm
            rw [hOGd]
            rw [copies_succ_eq] at hc1
            by_cases hcG : c < copies Om k
            · exact lt_of_lt_of_le' hcG (le_add_right' _ _)
            · obtain ⟨c', rfl⟩ := between_prefix (le_of_not_lt' hcG) hc1
              have hc' : c' < P 1 Om Z := (add_lt_add_left_iff _).mp hc1
              apply (add_lt_add_left_iff _).mpr
              cases c' with
              | Z => exact Z_lt_P' _ _ _
              | P j u v =>
                  rcases lt_inv _ _ _ _ _ _ hc' with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
                  · exact T.Lt.p_head _ _ _ _ _ _ h2
                  · apply T.Lt.p_mid
                    have hmemc : T.add (copies Om k) (P 1 u v) ∈ T.G1 0 (uncPart h) := by
                      rw [← hsplit, uncPart_add_unc hBu]
                      show _ ∈ T.G1 0 (T.add B (P 1 _ (uncPart R')))
                      rw [G1_add, G1_P0]; simp
                    have hmem : u ∈ T.G1 0 (uncPart h) :=
                      G1_trans 0 hmemc u (by simp [G1_add, G1_P0])
                    have hhn : T.isNF1 (P 0 h Z) := isNF1_head ha.nf
                    have hun : T.isNF1 u :=
                      isNF1_of_G1 (isNF1_arg (isNF1_psi_unc hhn)) u hmem
                    exact cnt_comp_lt_logA hhn hU hmem (Cnt_of_lt_Om (isNF1_desc hun) h2)
                  · exact absurd h2 (not_lt_Z' _)
      · obtain ⟨_, hee⟩ := pureB_true hp
        have hc : coefX k (P 0 h r) Z = Z := by simp [coefX, hp]
        rw [hc, OPowTimes_Z, T.add_Z, ← hee]
        exact le_refl' _

/-! ### `φ_k(e, 0)` for limit `e` -/

/-- Below `φ_k(e, 0)`, `e` a limit, everything is eventually below `φ_k(d', 0)`. -/
theorem phiLimZ (n : Nat) {e : T} (he : Good e) (hl : Lim e) {b : T} (hb : T.isNF1 b)
    (hlt : b < phi n e Z) :
    ∃ a, Good a ∧ a < e ∧
      ∀ d', Good d' → a ≤ d' → d' < e → (n = 0 → d' ≠ Z) → b ≤ phi n d' Z := by
  obtain ⟨h, r, rfl, hh0⟩ := lim_head he hl
  cases hp : pureB n (P 0 h r)
  · generalize hB : alphaHead n (P 0 h r) = B
    have hBh : B = takeW (predA n) h := by rw [← hB, alphaHead_P]
    have hBall : AllW (predA n) B := hBh ▸ takeW_all _ h
    have hc : coefX n (P 0 h r) Z = one := by simp [coefX, hp]; rfl
    rw [phi_eq_dflt n _ Z (by rintro ⟨_, _, _, e, _⟩; cases e), hc, OPowTimes_one, hB] at hlt
    have hsplit : T.add B (dropW (predA n) h) = h := by rw [hBh]; exact takeW_add_dropW _ h
    have hψB : P 0 B Z < P 0 h r := by
      have hBle := takeW_prefix_le (predA n) h
      rw [← hBh] at hBle
      rcases hBle with hlt' | heq
      · exact T.Lt.p_mid _ _ _ _ _ hlt'
      · subst heq
        cases r with
        | Z =>
            exfalso
            unfold pureB at hp
            rw [hB] at hp
            have h1 : decide (B ≠ Z) = true := decide_eq_true hh0
            have h2 : decide (P 0 B Z = P 0 B Z) = true := decide_eq_true rfl
            rw [h1, h2] at hp
            exact absurd hp (by decide)
        | P _ _ _ => exact T.Lt.p_tail _ _ _ _ (Z_lt_P' _ _ _)
    have hψBn : T.isNF1 (P 0 B Z) := by
      refine (isNF1_P_Z_iff 0 _).mpr ⟨?_, ?_⟩
      · have := isNF1_arg (isNF1_head he.nf)
        rw [← hsplit] at this
        exact isNF1_of_add_left this
      · intro x hx
        apply lt_prefix_of_comp hx (R := dropW (predA n) h)
        rw [hsplit]
        apply isNF1_G (isNF1_head he.nf) x
        rw [← hsplit, G1_add]
        exact List.mem_append_left _ hx
    have hψBg : Good (P 0 B Z) := ⟨hψBn, rfl, trivial⟩
    have ha0 := hl.succ_lt he hψBg hψB
    have hrange : ∀ d', Good d' → T.add (P 0 B Z) one ≤ d' → d' < P 0 h r →
        phi n d' Z = P 0 (T.add B (P 1 (OGd n d') Z)) Z := by
      intro d' hd' hle hlt'
      have hpre : P 0 B Z < d' := lt_of_lt_of_le' (lt_add_of_ne _ (by intro h; cases h)) hle
      have hBd : alphaHead n d' = B := by
        apply le_antisymm'
        · rw [← hB]; exact alphaHead_le n hd' he (Or.inl hlt')
        · have h1 := alphaHead_le n hψBg hd' (Or.inl hpre)
          rwa [alphaHead_P, takeW_of_all _ _ hBall] at h1
      have hnp : pureB n d' = false := by
        unfold pureB; rw [hBd]
        have : decide (d' = P 0 B Z) = false :=
          decide_eq_false (fun e => by rw [e] at hpre; exact lt_irr _ hpre)
        rw [this, Bool.and_false]
      have hc' : coefX n d' Z = one := by simp [coefX, hnp]; rfl
      rw [phi_eq_dflt n _ Z (by rintro ⟨_, _, _, e, _⟩; cases e), hc', OPowTimes_one, hBd]
    have hfin : ∀ a, Good a → T.add (P 0 B Z) one ≤ a → a < P 0 h r →
        (∀ d', Good d' → a ≤ d' → d' < P 0 h r → b < P 0 (T.add B (P 1 (OGd n d') Z)) Z) →
        ∃ a, Good a ∧ a < P 0 h r ∧
          ∀ d', Good d' → a ≤ d' → d' < P 0 h r → (n = 0 → d' ≠ Z) → b ≤ phi n d' Z := by
      intro a ha ha0' hae hall
      refine ⟨a, ha, hae, fun d' hd' had hd'e _ => ?_⟩
      rw [hrange d' hd' (le_tr ha0' had) hd'e]
      exact Or.inl (hall d' hd' had hd'e)
    cases b with
    | Z => exact ⟨_, good_add_one hψBg, ha0, fun _ _ _ _ _ => Z_le' _⟩
    | P i c r' =>
        obtain ⟨rfl, hc⟩ := lt_P0 hlt
        by_cases hcB : c < B
        · exact hfin _ (good_add_one hψBg) (le_refl' _) ha0
            (fun d' _ _ _ => T.Lt.p_mid _ _ _ _ _ (lt_add_of_lt _ _ hcB))
        · obtain ⟨c'', rfl⟩ := between_prefix (le_of_not_lt' hcB) hc
          have hc'' := (add_lt_add_left_iff _).mp hc
          cases c'' with
          | Z =>
              exact hfin _ (good_add_one hψBg) (le_refl' _) ha0
                (fun d' _ _ _ => T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr (Z_lt_P' _ _ _)))
          | P j x c3 =>
              rcases lt_inv _ _ _ _ _ _ hc'' with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
              · exact hfin _ (good_add_one hψBg) (le_refl' _) ha0
                  (fun d' _ _ _ => T.Lt.p_mid _ _ _ _ _
                    ((add_lt_add_left_iff _).mpr (T.Lt.p_head _ _ _ _ _ _ h2)))
              · have hxn : T.isNF1 x := by
                  apply isNF1_of_G1 (u := 0) (isNF1_arg hb) x
                  simp [G1_add, G1_P0]
                obtain ⟨a1, ha1, ha1e, _, hxa1⟩ := OGd_cont n he hl hxn h2
                have hfx : ∀ d', Good d' → T.add a1 one ≤ d' →
                    P 0 (T.add B (P 1 x c3)) r' < P 0 (T.add B (P 1 (OGd n d') Z)) Z :=
                  fun d' hd' had => T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr
                    (T.Lt.p_mid _ _ _ _ _ (lt_of_lt_of_le' hxa1
                      (OGd_le n (good_add_one ha1) hd' (fun _ => add_one_ne_Z a1) had))))
                have ha1s := hl.succ_lt he ha1 ha1e
                rcases lt_total_thm (T.add (P 0 B Z) one) (T.add a1 one) with hm | hm | hm
                · exact hfin _ (good_add_one ha1) (Or.inl hm) ha1s
                    (fun d' hd' had _ => hfx d' hd' had)
                · exact hfin _ (good_add_one hψBg) (le_refl' _) ha0
                    (fun d' hd' had _ => hfx d' hd' (le_tr (Or.inl hm) had))
                · exact hfin _ (good_add_one ha1) (Or.inr hm) ha1s
                    (fun d' hd' had _ => hfx d' hd' had)
              · exact absurd h2 (not_lt_Z' _)
  · obtain ⟨_, hee⟩ := pureB_true hp
    have hc : coefX n (P 0 h r) Z = Z := by simp [coefX, hp]
    rw [phi_eq_dflt n _ Z (by rintro ⟨_, _, _, e, _⟩; cases e), hc, OPowTimes_Z, T.add_Z,
      ← hee] at hlt
    have hbg : Good b := ⟨hb, Cnt_of_lt_Om (isNF1_desc hb) (lt_tr hlt (Cnt_lt_Om he.cnt))⟩
    exact ⟨b, hbg, hlt, fun d' hd' hbd _ hk => le_tr hbd (phi_index_infl n hd' hk)⟩

/-- **Limit exponents**. -/
theorem flLim (n : Nat) {e X : T} (he : Good e) (hl : Lim e) (hX : Good X) : FLStmt n e X := by
  have he0 : e ≠ Z := hl.1
  have hone_e : one < e := hl.one_lt he
  have he' : (if n = 0 then e else minus1 e) = e := by
    split
    · rfl
    · exact minus1_lim he hl
  have hEe : ∀ y, y ≠ Z → Eom (n + 1) e y = phi n e (minus1 y) := by
    intro y hy; rw [Eom_succ_ne n he0, if_neg hy, he']
  have happ : ∀ d, Good d → d ≠ Z → d < e → ∀ y, y ≠ Z →
      ∃ δ : Below (omegaPow e), E (n + 1) δ.1 y =
        phi n (if n = 0 then d else minus1 d) (minus1 y) := by
    intro d hd hd0 hde y hy
    refine ⟨⟨omegaPow d, good_omegaPow hd, omegaPow_lt_omegaPow hd he hde⟩, ?_⟩
    show E (n + 1) (omegaPow d) y = _
    rw [omegaPow_eq, E_P, E_Z, logA_omegaArg hd, Eom_succ_ne n hd0, if_neg hy]
  have hpick : ∀ a, Good a → a < e → ∃ d, Good d ∧ d ≠ Z ∧ d < e ∧
      a ≤ (if n = 0 then d else minus1 d) ∧ (if n = 0 then d else minus1 d) < e ∧
      Good (if n = 0 then d else minus1 d) ∧ (n = 0 → (if n = 0 then d else minus1 d) ≠ Z) := by
    intro a ha hae
    have has := hl.succ_lt he ha hae
    refine ⟨T.add a one, good_add_one ha, add_one_ne_Z a, has, ?_, ?_, ?_, ?_⟩
    · split
      · exact le_of_lt' (lt_add_of_ne a nofun)
      · exact le_minus1_succ ha
    · split
      · exact has
      · exact lt_of_le_of_lt' (minus1_le (good_add_one ha)) has
    · split
      · exact good_add_one ha
      · exact good_minus1 (good_add_one ha)
    · intro h0; rw [if_pos h0]; exact add_one_ne_Z a
  intro b hb hlt
  by_cases hX0 : X = Z
  · subst hX0
    have h0 : Eom (n + 1) e Z = Z := Eom_succ_Zarg n e
    rw [show T.add Z one = one from rfl, hEe one nofun,
      show minus1 one = Z from rfl] at hlt
    rw [h0, show T.add Z one = one from rfl]
    obtain ⟨a, ha, hae, hall⟩ := phiLimZ n he hl hb hlt
    obtain ⟨d, hd, hd0, hde, had', hd'e, hd'g, hd'k⟩ := hpick a ha hae
    obtain ⟨δ, hδ⟩ := happ d hd hd0 hde one nofun
    refine ⟨δ, ?_⟩
    show b ≤ E (n + 1) δ.1 one
    rw [hδ]
    exact hall _ hd'g had' hd'e hd'k
  · obtain ⟨Y, hYe, hY0, _⟩ := phi_lvl n e (minus1 X) he (good_minus1 hX)
    have hΦ : Eom (n + 1) e X = P 0 Y Z := by rw [hEe X hX0, hYe]
    have htop : Eom (n + 1) e (T.add X one) = P 0 (T.add Y (P 1 (OGd n e) Z)) Z := by
      rw [hEe _ (add_one_ne_Z X), minus1_add_one hX0, phi_add_one n (good_minus1 hX) hYe]
    rw [htop] at hlt
    rw [hΦ]
    have hval : ∀ d', Good d' → d' < e →
        phi n d' (minus1 (T.add (P 0 Y Z) one)) = P 0 (T.add Y (P 1 (OGd n d') Z)) Z := by
      intro d' hd' hd'e
      obtain ⟨Y', hY'e, hY'w, hBY'⟩ := phi_struct n hd' he (good_minus1 hX) hd'e
      rw [hYe] at hY'e
      injection hY'e with _ hYY' _
      subst hYY'
      rw [add_P, show T.add Z one = one from rfl, minus1_P0 hY0]
      have hD : headD n d' Y = Y := takeW_of_all _ _ hY'w
      have hlt' : alphaHead n d' < headD n d' Y := by rw [hD]; exact hBY'
      rw [phi_eq_abs n d' hlt', hD, if_pos rfl, OPowTimes_one]
    have hfind : ∀ a, Good a → a < e →
        (∀ d', Good d' → a ≤ d' → d' < e → b ≤ P 0 (T.add Y (P 1 (OGd n d') Z)) Z) →
        ∃ δ : Below (omegaPow e), b ≤ E (n + 1) δ.1 (T.add (P 0 Y Z) one) := by
      intro a ha hae hall
      obtain ⟨d, hd, hd0, hde, had', hd'e, hd'g, _⟩ := hpick a ha hae
      obtain ⟨δ, hδ⟩ := happ d hd hd0 hde _ (add_one_ne_Z _)
      refine ⟨δ, ?_⟩
      rw [hδ, hval _ hd'g hd'e]
      exact hall _ hd'g had' hd'e
    cases b with
    | Z => exact hfind one good_one hone_e (fun _ _ _ _ => Z_le' _)
    | P i c r =>
        obtain ⟨rfl, hc⟩ := lt_P0 hlt
        by_cases hcY : c < Y
        · exact hfind one good_one hone_e
            (fun d' _ _ _ => Or.inl (T.Lt.p_mid _ _ _ _ _ (lt_add_of_lt _ _ hcY)))
        · obtain ⟨c'', rfl⟩ := between_prefix (le_of_not_lt' hcY) hc
          have hc'' : c'' < P 1 (OGd n e) Z := (add_lt_add_left_iff _).mp hc
          cases c'' with
          | Z =>
              exact hfind one good_one hone_e (fun d' _ _ _ =>
                Or.inl (T.Lt.p_mid _ _ _ _ _ ((add_lt_add_left_iff _).mpr (Z_lt_P' _ _ _))))
          | P j x c3 =>
              rcases lt_inv _ _ _ _ _ _ hc'' with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
              · exact hfind one good_one hone_e (fun d' _ _ _ =>
                  Or.inl (T.Lt.p_mid _ _ _ _ _
                    ((add_lt_add_left_iff _).mpr (T.Lt.p_head _ _ _ _ _ _ h2))))
              · have hxn : T.isNF1 x := by
                  apply isNF1_of_G1 (u := 0) (isNF1_arg hb) x
                  simp [G1_add, G1_P0]
                obtain ⟨a1, ha1, ha1e, _, hxa1⟩ := OGd_cont n he hl hxn h2
                refine hfind (T.add a1 one) (good_add_one ha1) (hl.succ_lt he ha1 ha1e)
                  (fun d' hd' hle _ => ?_)
                apply Or.inl; apply T.Lt.p_mid; apply (add_lt_add_left_iff _).mpr
                apply T.Lt.p_mid
                exact lt_of_lt_of_le' hxa1
                  (OGd_le n (good_add_one ha1) hd' (fun _ => add_one_ne_Z a1) hle)
              · exact absurd h2 (not_lt_Z' _)

/-- **The fixed-point limit** for every positive exponent. -/
theorem fl (n : Nat) {e X : T} (he : Good e) (he0 : e ≠ Z) (hX : Good X) : FLStmt n e X := by
  rcases good_cases he with h | ⟨d, hd, rfl⟩ | hl
  · exact absurd h he0
  · by_cases hd0 : d = Z
    · subst hd0
      cases n with
      | zero => exact flEps hX
      | succ n => exact flGamma n hX
    · exact flSucc n hd hd0 hX
  · exact flLim n he hl hX

end Sem
