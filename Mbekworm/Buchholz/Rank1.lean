import Mbekworm.Buchholz.Base

open T

inductive Dom1 where
| Zero
| One
| ω
| Ω (l : Nat)
deriving DecidableEq

def T.dom1 : T → Dom1
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.dom1 s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | l + 1 => .Ω l
    | .One => .ω
    | .ω => .ω
    | .Ω l =>
      if s0 ≤ l then
        .ω
      else .Ω l
  else T.dom1 s2

theorem dom1_P0_of_Zero (s1 : T) (h : T.dom1 s1 = Dom1.Zero) : T.dom1 (P 0 s1 Z) = Dom1.One := by
  simp [T.dom1, h]

theorem dom1_P0_of_One (s1 : T) (h : T.dom1 s1 = Dom1.One) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_P0_of_ω (s1 : T) (h : T.dom1 s1 = Dom1.ω) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_P0_of_Ω (s1 : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_Psucc_of_Zero (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.Ω l0 := by
  simp [T.dom1, h]

theorem dom1_Psucc_of_One (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.One) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_Psucc_of_ω (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.ω) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_Psucc_of_Ω_le (l0 l1 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Ω l1) (hle : l0+1 ≤ l1) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  simp [T.dom1, h, hle]

theorem dom1_Psucc_of_Ω_gt (l0 l1 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Ω l1) (hgt : ¬ (l0+1 ≤ l1)) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.Ω l1 := by
  simp [T.dom1, h, hgt]

theorem dom1_P_tail (s0 : Nat) (s1 : T) (s20 : Nat) (s21 s22 : T) :
    T.dom1 (P s0 s1 (P s20 s21 s22)) = T.dom1 (P s20 s21 s22) := rfl

theorem dom1_P_of_One (s0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.One) : T.dom1 (P s0 s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_P_of_ω (s0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.ω) : T.dom1 (P s0 s1 Z) = Dom1.ω := by
  simp [T.dom1, h]

theorem dom1_P_of_Ω (s0 : Nat) (s1 : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) :
    T.dom1 (P s0 s1 Z) = if s0 ≤ l then Dom1.ω else Dom1.Ω l := by
  simp [T.dom1, h]

theorem dom1_ne_Zero_of_P (s0 : Nat) (s1 s2 : T) : T.dom1 (P s0 s1 s2) ≠ Dom1.Zero := by
  induction s2 generalizing s0 s1 with
  | Z =>
    cases s0 <;> cases h : T.dom1 s1 <;> simp [T.dom1, h] <;>
      split <;> simp
  | P s20 s21 s22 _ ih =>
    simpa [T.dom1] using ih s20 s21

theorem dom1_Zero_imp_eq_Z (x : T) (h : T.dom1 x = Dom1.Zero) : x = Z := by
  cases x with
  | Z => rfl
  | P x0 x1 x2 => exact absurd h (dom1_ne_Zero_of_P x0 x1 x2)

def T.fund1 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom1 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund1 s1 Z) Z) t
      | .ω => P s0 (T.fund1 s1 t) Z
      | .Ω l =>
        if s0 ≤ l then
          let F := fun x => P l (T.fund1 s1 x) Z
          P s0 (T.fund1 s1 (T.iter F t)) Z
        else P s0 (T.fund1 s1 t) Z
    else P s0 s1 (T.fund1 s2 t)

theorem fund1_P0_of_Zero (s1 t : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.fund1 (P 0 s1 Z) t = Z := by
  rw [T.fund1, h]; rfl

theorem fund1_P0_of_One (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P 0 s1 Z) t = T.mul (P 0 (T.fund1 s1 Z) Z) t := by
  rw [T.fund1, h]; rfl

theorem fund1_P0_of_ω (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P 0 s1 Z) t = P 0 (T.fund1 s1 t) Z := by
  rw [T.fund1, h]; rfl

theorem fund1_P0_of_Ω (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) :
    T.fund1 (P 0 s1 Z) t = P 0 (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t)) Z := by
  rw [T.fund1, h]; rfl

theorem fund1_Psucc_of_Zero (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.fund1 (P (l0+1) s1 Z) t = t := by
  rw [T.fund1, h]; rfl

theorem fund1_Psucc_of_One (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P (l0+1) s1 Z) t = T.mul (P (l0+1) (T.fund1 s1 Z) Z) t := by
  rw [T.fund1, h]; rfl

theorem fund1_Psucc_of_ω (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 t) Z := by
  rw [T.fund1, h]; rfl

theorem fund1_Psucc_of_Ω_le (l0 l1 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Ω l1) (hle : l0+1 ≤ l1) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 (T.iter (fun x => P l1 (T.fund1 s1 x) Z) t)) Z := by
  rw [T.fund1, h] <;> simp [hle]

theorem fund1_Psucc_of_Ω_gt (l0 l1 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Ω l1) (hgt : ¬ (l0+1 ≤ l1)) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 t) Z := by
  rw [T.fund1, h] <;> simp [hgt]

theorem fund1_P_tail (s0 : Nat) (s1 : T) (t : T) (s20 : Nat) (s21 s22 : T) :
    T.fund1 (P s0 s1 (P s20 s21 s22)) t = P s0 s1 (T.fund1 (P s20 s21 s22) t) := rfl

theorem fund1_P_of_One (s0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P s0 s1 Z) t = T.mul (P s0 (T.fund1 s1 Z) Z) t := by
  cases s0 <;> rw [T.fund1, h] <;> rfl

theorem fund1_P_of_ω (s0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 t) Z := by
  cases s0 <;> rw [T.fund1, h] <;> rfl

theorem fund1_P_of_Ω_le (s0 : Nat) (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) (hle : s0 ≤ l) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t)) Z := by
  cases s0 <;> rw [T.fund1, h] <;> simp [hle]

theorem fund1_P_of_Ω_gt (s0 : Nat) (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) (hgt : ¬ s0 ≤ l) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 t) Z := by
  cases s0 <;> rw [T.fund1, h] <;> simp [hgt]

inductive T.index_Prop1 (v : Nat) : T → Prop where
| z : T.index_Prop1 v Z
| p (s0 : Nat) (s1 s2 : T) : s0 ≤ v → T.index_Prop1 v s2 → T.index_Prop1 v (P s0 s1 s2)

theorem index_Prop1_lt_succ (l : Nat) (t : T) (h : T.index_Prop1 l t) :
    t < P (l+1) Z Z := by
  cases h with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p _ _ _ h _ => exact T.Lt.p_head _ _ _ _ _ _ (Nat.lt_succ_of_le h)

theorem iter_index_Prop1 (l : Nat) (g : T → T) (hg : ∀ x, ∃ y, g x = P l y Z) (t : T) :
    T.index_Prop1 l (T.iter g t) := by
  cases t with
  | Z => exact T.index_Prop1.z
  | P n a b =>
      obtain ⟨y, hy⟩ := hg (T.iter g b)
      rw [T.iter, hy]
      exact T.index_Prop1.p _ _ _ (Nat.le_refl _) T.index_Prop1.z

def T.ValidArg1 (s t : T) : Prop :=
  match T.dom1 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .Ω l => index_Prop1 l t

theorem ValidArg1_Zero_iff (s t : T) (h : T.dom1 s = Dom1.Zero) : T.ValidArg1 s t ↔ False := by
  simp [T.ValidArg1, h]

theorem ValidArg1_One_iff (s t : T) (h : T.dom1 s = Dom1.One) : T.ValidArg1 s t ↔ t = Z := by
  simp [T.ValidArg1, h]

theorem ValidArg1_ω_iff (s t : T) (h : T.dom1 s = Dom1.ω) : T.ValidArg1 s t ↔ T.IsN t := by
  simp [T.ValidArg1, h]

theorem ValidArg1_Ω_iff (s t : T) (l : Nat) (h : T.dom1 s = Dom1.Ω l) : T.ValidArg1 s t ↔ T.index_Prop1 l t := by
  simp [T.ValidArg1, h]

theorem T.ValidArg1_tail_iff (s0 : Nat) (s1 : T) (s20 : Nat) (s21 s22 t : T) :
    T.ValidArg1 (P s0 s1 (P s20 s21 s22)) t ↔ T.ValidArg1 (P s20 s21 s22) t := by
  rfl

theorem T.fund1_fall (s t : T) (hv : T.ValidArg1 s t) : T.fund1 s t < s := by
  induction s generalizing t with
  | Z => exact False.elim hv
  | P s0 s1 s2 ih1 ih2 =>
      cases s2 with
      | Z =>
          cases hd : T.dom1 s1 with
          | Zero =>
              have hs1 := dom1_Zero_imp_eq_Z s1 hd
              subst s1
              cases s0 with
              | zero => exact T.Lt.Z_lt_P _ _ _
              | succ l => exact index_Prop1_lt_succ l t hv
          | One =>
              rw [fund1_P_of_One s0 s1 t hd]
              have hlt := ih1 Z (by simp [T.ValidArg1, hd])
              have hn : T.IsN t := by simpa [T.ValidArg1, T.dom1, hd] using hv
              rcases mul_shape s0 (T.fund1 s1 Z) t hn with h | ⟨u, h⟩
              · rw [h]; exact T.Lt.Z_lt_P _ _ _
              · rw [h]; exact T.Lt.p_mid _ _ _ _ _ hlt
          | ω =>
              rw [fund1_P_of_ω s0 s1 t hd]
              exact T.Lt.p_mid _ _ _ _ _ (ih1 t (by simpa [T.ValidArg1, T.dom1, hd] using hv))
          | Ω l =>
              by_cases hle : s0 ≤ l
              · rw [fund1_P_of_Ω_le s0 s1 t l hd hle]
                apply T.Lt.p_mid
                apply ih1
                simpa [T.ValidArg1, hd] using
                  iter_index_Prop1 l _ (fun x => ⟨T.fund1 s1 x, rfl⟩) t
              · rw [fund1_P_of_Ω_gt s0 s1 t l hd hle]
                exact T.Lt.p_mid _ _ _ _ _
                  (ih1 t (by simpa [T.ValidArg1, T.dom1, hd, hle] using hv))
      | P a b c => exact T.Lt.p_tail _ _ _ _ (ih2 t hv)

theorem iter_F_step_mono (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (n : Nat) :
    T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n) <
      T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n+1)) := by
  have hv (t : T) : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t) := by
    simpa [T.ValidArg1, hd] using
      iter_index_Prop1 l _ (fun x => ⟨T.fund1 s1 x, rfl⟩) t
  induction n with
  | zero => exact T.Lt.Z_lt_P _ _ _
  | succ n ih => exact T.Lt.p_mid _ _ _ _ _ (mono1 _ _ ih (hv _) (hv _))

theorem iter_F_strict_mono_ofNat (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (n1 : Nat) :
    ∀ n0, n0 < n1 → T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n0) <
      T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n1) := by
  induction n1 with
  | zero => intro n0 h; exact False.elim (by omega)
  | succ n ih =>
      intro n0 h
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
      · exact lt_trans_thm _ _ _ (ih n0 h) (iter_F_step_mono s1 l hd mono1 n)
      · exact iter_F_step_mono s1 l hd mono1 _

theorem iter_F_strict_mono (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (t0 t1 : T) (hlt : t0 < t1) (hIsN0 : T.IsN t0) (hIsN1 : T.IsN t1) :
    T.iter (fun x => P l (T.fund1 s1 x) Z) t0 < T.iter (fun x => P l (T.fund1 s1 x) Z) t1 := by
  obtain ⟨n0, rfl⟩ := IsN_exists_ofNat hIsN0
  obtain ⟨n1, rfl⟩ := IsN_exists_ofNat hIsN1
  exact iter_F_strict_mono_ofNat s1 l hd mono1 n1 n0 (ofNat_reflect_lt hlt)

theorem T.fund1_strict_mono_dec (s t0 t1 : T) (hlt : t0 < t1)
    (ht0 : T.ValidArg1 s t0) (ht1 : T.ValidArg1 s t1) :
    T.fund1 s t0 < T.fund1 s t1 := by
  induction s generalizing t0 t1 with
  | Z => exact False.elim ht0
  | P s0 s1 s2 ih1 ih2 =>
      cases s2 with
      | Z =>
          cases hd : T.dom1 s1 with
          | Zero =>
              cases s0 with
              | zero =>
                  have h0 : t0 = Z := by simpa [T.ValidArg1, T.dom1, hd] using ht0
                  have h1 : t1 = Z := by simpa [T.ValidArg1, T.dom1, hd] using ht1
                  subst t0; subst t1
                  exact False.elim (lt_irrefl_thm _ hlt)
              | succ l => simpa [fund1_Psucc_of_Zero, hd] using hlt
          | One =>
              have hn0 : T.IsN t0 := by simpa [T.ValidArg1, T.dom1, hd] using ht0
              have hn1 : T.IsN t1 := by simpa [T.ValidArg1, T.dom1, hd] using ht1
              obtain ⟨n0, rfl⟩ := IsN_exists_ofNat hn0
              obtain ⟨n1, rfl⟩ := IsN_exists_ofNat hn1
              rw [fund1_P_of_One s0 s1 _ hd, fund1_P_of_One s0 s1 _ hd]
              exact mul_ofNat_strict_mono _ (by intro h; cases h) n1 n0 (ofNat_reflect_lt hlt)
          | ω =>
              rw [fund1_P_of_ω s0 s1 t0 hd, fund1_P_of_ω s0 s1 t1 hd]
              exact T.Lt.p_mid _ _ _ _ _ (ih1 _ _ hlt
                (by simpa [T.ValidArg1, T.dom1, hd] using ht0)
                (by simpa [T.ValidArg1, T.dom1, hd] using ht1))
          | Ω l =>
              by_cases hle : s0 ≤ l
              · have hv (t : T) : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t) := by
                  simpa [T.ValidArg1, hd] using
                    iter_index_Prop1 l _ (fun x => ⟨T.fund1 s1 x, rfl⟩) t
                have hi := iter_F_strict_mono s1 l hd ih1 t0 t1 hlt
                  (by simpa [T.ValidArg1, T.dom1, hd, hle] using ht0)
                  (by simpa [T.ValidArg1, T.dom1, hd, hle] using ht1)
                rw [fund1_P_of_Ω_le s0 s1 t0 l hd hle, fund1_P_of_Ω_le s0 s1 t1 l hd hle]
                exact T.Lt.p_mid _ _ _ _ _ (ih1 _ _ hi (hv _) (hv _))
              · rw [fund1_P_of_Ω_gt s0 s1 t0 l hd hle, fund1_P_of_Ω_gt s0 s1 t1 l hd hle]
                exact T.Lt.p_mid _ _ _ _ _ (ih1 _ _ hlt
                  (by simpa [T.ValidArg1, T.dom1, hd, hle] using ht0)
                  (by simpa [T.ValidArg1, T.dom1, hd, hle] using ht1))
      | P a b c => exact T.Lt.p_tail _ _ _ _ (ih2 _ _ hlt ht0 ht1)

def T.G1 (u : Nat) (s : T) : List T :=
  match s with
  | Z => []
  | P s0 s1 s2 =>
    let Gs2 := T.G1 u s2
    if u ≤ s0 then
      [s1] ++ T.G1 u s1 ++ Gs2
    else Gs2

inductive T.isNF1 : T → Prop where
| z : T.isNF1 Z
| p (s0 : Nat) (s1 s2 : T) (hs1 : T.isNF1 s1) (hs2 : T.isNF1 s2)
  (h1 : ∀ x : T, x ∈ T.G1 s0 s1 → x < s1)
  (h2 : T.head s2 ≤ P s0 s1 Z) :
  T.isNF1 (P s0 s1 s2)

def T.decidableBAllLt (l : List T) (y : T) : Decidable (∀ x ∈ l, x < y) :=
  match l with
  | [] => isTrue (fun _x hx => absurd hx List.not_mem_nil)
  | a :: as =>
    match (inferInstance : Decidable (a < y)) with
    | isFalse hna => isFalse (fun h => hna (h a List.mem_cons_self))
    | isTrue ha =>
      match T.decidableBAllLt as y with
      | isFalse hnas => isFalse (fun h => hnas (fun x hx => h x (List.mem_cons_of_mem a hx)))
      | isTrue has => isTrue (fun x hx =>
          (List.mem_cons.mp hx).elim (fun heq => heq ▸ ha) (fun hx' => has x hx'))

def T.decIsNF (s : T) : Decidable (T.isNF1 s) :=
  match s with
  | Z => isTrue T.isNF1.z
  | P s0 s1 s2 =>
    match T.decIsNF s1 with
    | isFalse hn1 => isFalse (fun h => by
        cases h with
        | p _ _ _ hs1 _ _ _ => exact hn1 hs1)
    | isTrue hs1 =>
      match T.decIsNF s2 with
      | isFalse hn2 => isFalse (fun h => by
          cases h with
          | p _ _ _ _ hs2 _ _ => exact hn2 hs2)
      | isTrue hs2 =>
        match T.decidableBAllLt (T.G1 s0 s1) s1 with
        | isFalse hn3 => isFalse (fun h => by
            cases h with
            | p _ _ _ _ _ h1 _ => exact hn3 h1)
        | isTrue h1 =>
          match (inferInstance : Decidable (T.head s2 ≤ P s0 s1 Z)) with
          | isFalse hn4 => isFalse (fun h => by
              cases h with
              | p _ _ _ _ _ _ h2 => exact hn4 h2)
          | isTrue h2 => isTrue (T.isNF1.p s0 s1 s2 hs1 hs2 h1 h2)

instance (s : T) : Decidable (T.isNF1 s) := T.decIsNF s

theorem T.isNF1_P_inv (s0 : Nat) (s1 s2 : T) (h : T.isNF1 (P s0 s1 s2)) :
    T.isNF1 s1 ∧ T.isNF1 s2 ∧ (∀ x : T, x ∈ T.G1 s0 s1 → x < s1) ∧ T.head s2 ≤ P s0 s1 Z := by
  cases h; exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

def T.GZ (u : Nat) (z : T) : List T := T.G1 u z ++ [Z]

def T.SDom (z b a : T) : Prop :=
  b < a ∧ ∀ (u : Nat) (c : T), b ≤ c → c ≤ a →
    T.listLe (T.G1 u b) (T.G1 u c ++ T.GZ u z)

theorem SDom_G1_lt_a (z b a : T) (u : Nat) (hb : T.SDom z b a)
    (hGa : ∀ x ∈ T.G1 u a, x < a) (hGz : ∀ x ∈ T.GZ u z, x < b) :
    ∀ y ∈ T.G1 u b, y < a := by
  intro y hy
  obtain ⟨w, hw, hyw⟩ := hb.2 u a (Or.inl hb.1) (Or.inr rfl) y hy
  apply lt_of_le_of_lt_thm T y w a hyw
  rcases List.mem_append.mp hw with hw | hw
  · exact hGa w hw
  · exact lt_trans_thm _ _ _ (hGz w hw) hb.1

theorem find_violating_source (u : Nat) (b : T) :
    ∀ c₀ : T, ∀ w : T, w ∈ T.G1 u c₀ → b ≤ w →
      ∃ c : T, c ∈ T.G1 u c₀ ∧ b ≤ c ∧ (∀ x ∈ T.G1 u c, x < b) := by
  intro c₀
  induction c₀ with
  | Z => intro w hw _; cases hw
  | P p0 p1 p2 ih1 ih2 =>
      intro w hw hbw
      by_cases hup : u ≤ p0
      · rw [T.G1.eq_2, ite_eq_left hup] at hw ⊢
        have lift1 (x : T) (hx : x ∈ T.G1 u p1) (hb : b ≤ x) :
            ∃ c, c ∈ [p1] ++ T.G1 u p1 ++ T.G1 u p2 ∧ b ≤ c ∧
              ∀ y ∈ T.G1 u c, y < b := by
          obtain ⟨c, hc, hbc, hgood⟩ := ih1 x hx hb
          exact ⟨c, by simp [hc], hbc, hgood⟩
        rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · have he := List.mem_singleton.mp hw
            subst w
            by_cases hviol : ∃ x ∈ T.G1 u p1, b ≤ x
            · obtain ⟨x, hx, hb⟩ := hviol
              exact lift1 x hx hb
            · refine ⟨p1, by simp, hbw, ?_⟩
              intro x hx
              rcases lt_total_thm x b with h | h | h
              · exact h
              · exact False.elim (hviol ⟨x, hx, Or.inl h⟩)
              · exact False.elim (hviol ⟨x, hx, Or.inr h.symm⟩)
          · exact lift1 w hw hbw
        · obtain ⟨c, hc, hbc, hgood⟩ := ih2 w hw hbw
          exact ⟨c, by simp [hc], hbc, hgood⟩
      · rw [T.G1.eq_2, ite_eq_right hup] at hw ⊢
        exact ih2 w hw hbw

theorem lemma_3_4 (z b a : T) (u : Nat) (hSDom : T.SDom z b a)
    (hGa : ∀ x ∈ T.G1 u a, x < a) (hGz : ∀ x ∈ T.GZ u z, x < b) :
    ∀ y ∈ T.G1 u b, y < b := by
  intro y hy
  have step (hby : b ≤ y) : y < b := by
    obtain ⟨c, hc, hbc, hgood⟩ := find_violating_source u b b y hy hby
    have hca := SDom_G1_lt_a z b a u hSDom hGa hGz c hc
    obtain ⟨w, hw, hyw⟩ := hSDom.2 u c hbc (Or.inl hca) y hy
    apply lt_of_le_of_lt_thm T y w b hyw
    exact (List.mem_append.mp hw).elim (hgood w) (hGz w)
  rcases lt_total_thm y b with h | h | h
  · exact h
  · exact step (Or.inl h)
  · exact step (Or.inr h.symm)

theorem SDom_tail (z b0 b : T) (s0 : Nat) (s1 : T) (hb0 : T.SDom z b0 b) :
    T.SDom z (P s0 s1 b0) (P s0 s1 b) := by
  refine ⟨T.Lt.p_tail _ _ _ _ hb0.1, ?_⟩
  intro u c hc1 hc2
  rcases hc1 with hc1 | rfl
  · obtain ⟨c0, rfl, hlo, hhi⟩ : ∃ c0, c = P s0 s1 c0 ∧ b0 ≤ c0 ∧ c0 ≤ b := by
      rcases hc2 with hc2 | rfl
      · obtain ⟨c0, rfl, hlo, hhi⟩ := sandwich_tail s0 s1 b0 c b hc1 hc2
        exact ⟨c0, rfl, Or.inl hlo, Or.inl hhi⟩
      · exact ⟨b, rfl, Or.inl hb0.1, Or.inr rfl⟩
    have hh := hb0.2 u c0 hlo hhi
    by_cases hus : u ≤ s0
    · simpa [T.G1, hus, List.append_assoc] using
        listLe_append_congr ([s1] ++ T.G1 u s1) _ _ hh
    · simpa [T.G1, hus] using hh
  · exact listLe_self_append _ _

theorem G1_PZ_pos (u p0 : Nat) (p1 : T) (h : u ≤ p0) :
    T.G1 u (P p0 p1 Z) = [p1] ++ T.G1 u p1 := by
  simp [T.G1, h]

theorem G1_PZ_neg (u p0 : Nat) (p1 : T) (h : ¬ u ≤ p0) :
    T.G1 u (P p0 p1 Z) = [] := by
  simp [T.G1, h]

theorem SDom_wrap (z b0 b : T) (s0 : Nat) (hb0 : T.SDom z b0 b) :
    T.SDom z (P s0 b0 Z) (P s0 b Z) := by
  refine ⟨T.Lt.p_mid _ _ _ _ _ hb0.1, ?_⟩
  intro u c hc1 hc2
  rcases hc1 with hc1 | rfl
  · obtain ⟨c1, c2, rfl, hlo, hhi⟩ :
        ∃ c1 c2, c = P s0 c1 c2 ∧ b0 ≤ c1 ∧ c1 ≤ b := by
      rcases hc2 with hc2 | rfl
      · obtain ⟨c1, c2, rfl, hlo, hhi⟩ := sandwich_mid s0 b0 b c hb0.1 hc1 hc2
        exact ⟨c1, c2, rfl, hlo, Or.inl hhi⟩
      · exact ⟨b, Z, rfl, Or.inl hb0.1, Or.inr rfl⟩
    have hh := hb0.2 u c1 hlo hhi
    by_cases hus : u ≤ s0
    · rw [G1_PZ_pos u s0 b0 hus]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have he := List.mem_singleton.mp hx
        subst x
        exact ⟨c1, by simp [T.G1, hus], hlo⟩
      · obtain ⟨w, hw, hxw⟩ := hh x hx
        refine ⟨w, ?_, hxw⟩
        rcases List.mem_append.mp hw with hw | hw <;> simp [T.G1, hus, hw]
    · simp [T.listLe, T.G1, hus]
  · exact listLe_self_append _ _

theorem T.isNF1_tail_le : ∀ x : T, T.isNF1 x → ∀ x0 x1 x2, x = P x0 x1 x2 → x2 ≤ P x0 x1 x2 := by
  intro x
  induction x with
  | Z => intro _ x0 x1 x2 he; cases he
  | P a0 a1 a2 _ ih =>
      intro ha x0 x1 x2 he
      cases he
      obtain ⟨_, hs2, _, hh⟩ := T.isNF1_P_inv a0 a1 a2 ha
      cases a2 with
      | Z => exact T.Z_le _
      | P b0 b1 b2 =>
          rcases hh with hh | hh
          · cases hh with
            | p_head _ _ _ _ _ _ h => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h)
            | p_mid _ _ _ _ _ h => exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
            | p_tail _ _ _ _ h => cases h
          · cases hh
            rcases ih hs2 a0 a1 b2 rfl with h | h
            · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
            · rw [← h]; exact Or.inr h

theorem IsN_G1_eq_Z (t : T) (h : T.IsN t) (u : Nat) : ∀ x ∈ T.G1 u t, x = Z := by
  induction h with
  | zero => intro x hx; cases hx
  | succ t _ ih =>
      intro x hx
      by_cases hu : u ≤ 0
      · simp [T.G1, hu] at hx
        exact hx.elim id (ih x)
      · exact ih x (by simpa [T.G1, hu] using hx)

theorem index_Prop1_G1_empty (l : Nat) (t : T) (h : T.index_Prop1 l t) (u : Nat) (hlu : l < u) :
    T.G1 u t = [] := by
  induction h with
  | z => rfl
  | p s0 s1 s2 hle _ ih =>
      have hn : ¬ u ≤ s0 := by omega
      simp [T.G1, hn, ih]

theorem SDom_G1_lt_of_zero_support (z b a : T) (u : Nat) (hb : T.SDom z b a)
    (hGa : ∀ x ∈ T.G1 u a, x < a) (hGz : ∀ x ∈ T.G1 u z, x = Z) :
    ∀ x ∈ T.G1 u b, x < b := by
  cases b with
  | Z => intro x hx; cases hx
  | P p c d =>
      apply lemma_3_4 z _ a u hb hGa
      intro x hx
      rw [(List.mem_append.mp hx).elim (hGz x) List.mem_singleton.mp]
      exact T.Lt.Z_lt_P _ _ _

theorem mul_isNF1_and_head (s0 : Nat) (c : T) (hc : T.isNF1 c) (h1c : ∀ x ∈ T.G1 s0 c, x < c) :
    ∀ n : Nat, T.isNF1 (T.mul (P s0 c Z) (T.ofNat n)) ∧
      T.head (T.mul (P s0 c Z) (T.ofNat n)) ≤ P s0 c Z := by
  intro n
  induction n with
  | zero => exact ⟨T.isNF1.z, T.Z_le _⟩
  | succ n ih =>
      rw [mul_succ_shape]
      exact ⟨T.isNF1.p _ _ _ hc ih.1 h1c ih.2, Or.inr rfl⟩

theorem GZ_Z_mem (u : Nat) (w : T) : Z ∈ T.GZ u w := by
  simp [T.GZ]

theorem GZ_Z_le (u : Nat) (w : T) : T.listLe (T.GZ u Z) (T.GZ u w) := by
  intro x hx
  have he : x = Z := by simpa [T.GZ, T.G1] using hx
  exact ⟨Z, GZ_Z_mem u w, Or.inr he⟩

theorem GZ_ofNat_le (u n : Nat) (w : T) : T.listLe (T.GZ u (T.ofNat n)) (T.GZ u w) := by
  intro x hx
  refine ⟨Z, GZ_Z_mem u w, Or.inr ?_⟩
  exact (List.mem_append.mp hx).elim
    (IsN_G1_eq_Z _ (ofNat_IsN n) u x) List.mem_singleton.mp

theorem G1_P_pos (u p0 : Nat) (p1 p2 : T) (h : u ≤ p0) :
    T.G1 u (P p0 p1 p2) = [p1] ++ T.G1 u p1 ++ T.G1 u p2 := by
  simp [T.G1, h]

theorem mul_SDom (s0 : Nat) (c s1 : T) (hSDc : T.SDom Z c s1) :
    ∀ n : Nat, T.SDom (T.ofNat n) (T.mul (P s0 c Z) (T.ofNat n)) (P s0 s1 Z) := by
  intro n
  induction n with
  | zero =>
      refine ⟨T.Lt.Z_lt_P _ _ _, ?_⟩
      intro u d _ _ x hx
      cases hx
  | succ n ih =>
      rw [mul_succ_shape]
      refine ⟨T.Lt.p_mid _ _ _ _ _ hSDc.1, ?_⟩
      intro u d hlo hhi
      rcases hlo with hlo | rfl
      · have hMd := lt_trans_thm _ _ _ (tail_lt_wrap s0 c n) hlo
        have htail := listLe_trans _ _ _ (ih.2 u d (Or.inl hMd) hhi)
          (listLe_append_congr _ _ _ (GZ_ofNat_le u n (T.ofNat (n + 1))))
        obtain ⟨d1, d2, rfl, hcd, hds⟩ :
            ∃ d1 d2, d = P s0 d1 d2 ∧ c ≤ d1 ∧ d1 ≤ s1 := by
          rcases hhi with hhi | rfl
          · obtain ⟨d1, d2, rfl, hh⟩ := sandwich_mid_tail s0 c _ s1 d hlo hhi
            rcases hh with ⟨hc, hs⟩ | ⟨rfl, _⟩
            · exact ⟨d1, d2, rfl, Or.inl hc, Or.inl hs⟩
            · exact ⟨_, d2, rfl, Or.inr rfl, Or.inl hSDc.1⟩
          · exact ⟨s1, Z, rfl, Or.inl hSDc.1, Or.inr rfl⟩
        by_cases hus : u ≤ s0
        · rw [G1_P_pos u s0 c _ hus]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · have he := List.mem_singleton.mp hx
              subst x
              exact ⟨d1, by simp [T.G1, hus], hcd⟩
            · obtain ⟨w, hw, hxw⟩ := hSDc.2 u d1 hcd hds x hx
              rcases List.mem_append.mp hw with hw | hw
              · exact ⟨w, by simp [T.G1, hus, hw], hxw⟩
              · have he : w = Z := by simpa [T.GZ, T.G1] using hw
                exact ⟨Z, List.mem_append_right _ (GZ_Z_mem _ _), he ▸ hxw⟩
          · exact htail x hx
        · simpa [T.G1, hus] using htail
      · exact listLe_self_append _ _

theorem GZ_z_sub_self (u : Nat) (z : T) : T.listLe (T.G1 u z) (T.GZ u z) := by
  intro x hx
  exact ⟨x, List.mem_append_left [Z] hx, Or.inr rfl⟩

theorem G1_antitone (u v : Nat) (huv : u ≤ v) (s : T) :
    ∀ x ∈ T.G1 v s, x ∈ T.G1 u s := by
  induction s with
  | Z => exact fun _ hx => hx
  | P s0 s1 s2 ih1 ih2 =>
      intro x hx
      by_cases hv : v ≤ s0
      · have hu := Nat.le_trans huv hv
        simp only [T.G1, ite_eq_left hv, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · simp [T.G1, hu, List.mem_singleton.mp hx]
        · simp [T.G1, hu, ih1 x hx]
        · simp [T.G1, hu, ih2 x hx]
      · have hx2 := ih2 x (by simpa [T.G1, hv] using hx)
        by_cases hu : u ≤ s0 <;> simp [T.G1, hu, hx2]

theorem SDom_wrap_transfer (z w b a : T) (k : Nat) (h : T.SDom w b a)
    (hsupport : ∀ u, u ≤ k → ∀ c, P k b Z ≤ c → c ≤ P k a Z →
      T.listLe (T.GZ u w) (T.G1 u c ++ T.GZ u z)) :
    T.SDom z (P k b Z) (P k a Z) := by
  have hw := SDom_wrap w b a k h
  refine ⟨hw.1, ?_⟩
  intro u c hbc hca x hx
  by_cases hu : u ≤ k
  · obtain ⟨y, hy, hxy⟩ := hw.2 u c hbc hca x hx
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨y, List.mem_append_left _ hy, hxy⟩
    · obtain ⟨v, hv, hyv⟩ := hsupport u hu c hbc hca y hy
      exact ⟨v, hv, partial_order.trans x y v hxy hyv⟩
  · simp [T.G1, hu] at hx

theorem iteration_master (a : T) (k l : Nat) (hkl : k ≤ l)
    (hd : T.dom1 a = Dom1.Ω l)
    (hbound : ∀ x ∈ T.G1 k a, x < a)
    (ih : ∀ z, T.isNF1 z → T.ValidArg1 a z →
      T.isNF1 (T.fund1 a z) ∧ T.SDom z (T.fund1 a z) a) :
    ∀ n, let w := T.iter (fun x => P l (T.fund1 a x) Z) (T.ofNat n)
      T.isNF1 w ∧ T.isNF1 (T.fund1 a w) ∧
      (∀ x ∈ T.G1 k (T.fund1 a w), x < T.fund1 a w) ∧
      T.SDom (T.ofNat n) (P k (T.fund1 a w) Z) (P k a Z) := by
  intro n
  induction n with
  | zero =>
      have hv := (ValidArg1_Ω_iff a Z l hd).mpr T.index_Prop1.z
      obtain ⟨hc, hs⟩ := ih Z T.isNF1.z hv
      exact ⟨T.isNF1.z, hc,
        SDom_G1_lt_of_zero_support Z _ a k hs hbound (by intro x hx; cases hx),
        SDom_wrap Z _ a k hs⟩
  | succ n hn =>
      let w := T.iter (fun x => P l (T.fund1 a x) Z) (T.ofNat n)
      let b := T.fund1 a w
      have hw : T.isNF1 (P l b Z) :=
        T.isNF1.p l b Z hn.2.1 T.isNF1.z
          (fun x hx => hn.2.2.1 x (G1_antitone k l hkl b x hx)) (T.Z_le _)
      have hv := (ValidArg1_Ω_iff a (P l b Z) l hd).mpr
        (T.index_Prop1.p l b Z (Nat.le_refl l) T.index_Prop1.z)
      obtain ⟨hc, hs⟩ := ih (P l b Z) hw hv
      have hb : b < T.fund1 a (P l b Z) := by
        apply T.fund1_strict_mono_dec a
        · exact iter_F_step_mono a l hd (T.fund1_strict_mono_dec a) n
        · exact (ValidArg1_Ω_iff a w l hd).mpr
            (iter_index_Prop1 l _ (fun x => ⟨T.fund1 a x, rfl⟩) (T.ofNat n))
        · exact hv
      refine ⟨hw, hc, ?_, ?_⟩
      · apply lemma_3_4 (P l b Z) _ a k hs hbound
        intro x hx
        simp only [T.GZ, G1_PZ_pos k l b hkl, List.mem_append, List.mem_singleton] at hx
        rcases hx with (rfl | hx) | rfl
        · exact hb
        · exact lt_trans_thm _ _ _ (hn.2.2.1 x hx) hb
        · exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le b) hb
      · apply SDom_wrap_transfer (T.ofNat (n + 1)) (P l b Z) _ a k hs
        intro u hu c hbc hca x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [G1_PZ_pos u l b (Nat.le_trans hu hkl), ← G1_PZ_pos u k b hu] at hx
          have hprev : P k b Z ≤ c := Or.inl
            (lt_of_lt_of_le_thm T _ _ c (T.Lt.p_mid k b _ Z Z hb) hbc)
          exact listLe_trans _ _ _ (hn.2.2.2.2 u c hprev hca)
            (listLe_append_congr _ _ _ (GZ_ofNat_le u n (T.ofNat (n + 1)))) x hx
        · exact ⟨Z, List.mem_append_right _ (GZ_Z_mem _ _), Or.inr (List.mem_singleton.mp hx)⟩

theorem master (a : T) : ∀ z : T, T.isNF1 a → T.isNF1 z → T.ValidArg1 a z →
    T.isNF1 (T.fund1 a z) ∧ T.SDom z (T.fund1 a z) a := by
  induction a with
  | Z => intro z _ _ hv; exact False.elim hv
  | P a0 a1 a2 ih1 ih2 =>
      intro z ha hz hv
      obtain ⟨ha1, ha2, hg, hh⟩ := T.isNF1_P_inv a0 a1 a2 ha
      cases a2 with
      | Z =>
          cases hd : T.dom1 a1 with
          | Zero =>
              cases a0 with
              | zero =>
                  rw [fund1_P0_of_Zero a1 z hd]
                  refine ⟨T.isNF1.z, T.Lt.Z_lt_P _ _ _, ?_⟩
                  intro u c _ _ x hx
                  cases hx
              | succ l =>
                  have hf := T.fund1_fall (P (l + 1) a1 Z) z hv
                  rw [fund1_Psucc_of_Zero l a1 z hd] at hf ⊢
                  refine ⟨hz, hf, ?_⟩
                  intro u c _ _ x hx
                  exact ⟨x, by simp [T.GZ, hx], Or.inr rfl⟩
          | One =>
              obtain ⟨hc, hs⟩ := ih1 Z ha1 T.isNF1.z (by simp [T.ValidArg1, hd])
              have hn : T.IsN z := by simpa [T.ValidArg1, T.dom1, hd] using hv
              obtain ⟨n, rfl⟩ := IsN_exists_ofNat hn
              have hb := SDom_G1_lt_of_zero_support Z _ a1 a0 hs hg (by intro x hx; cases hx)
              rw [fund1_P_of_One a0 a1 _ hd]
              exact ⟨(mul_isNF1_and_head a0 _ hc hb n).1, mul_SDom a0 _ a1 hs n⟩
          | ω =>
              have hn : T.IsN z := by simpa [T.ValidArg1, T.dom1, hd] using hv
              obtain ⟨hc, hs⟩ := ih1 z ha1 hz (by simpa [T.ValidArg1, hd] using hn)
              have hb := SDom_G1_lt_of_zero_support z _ a1 a0 hs hg (IsN_G1_eq_Z z hn a0)
              rw [fund1_P_of_ω a0 a1 z hd]
              exact ⟨T.isNF1.p _ _ _ hc T.isNF1.z hb (T.Z_le _), SDom_wrap z _ a1 a0 hs⟩
          | Ω l =>
              by_cases hle : a0 ≤ l
              · have hn : T.IsN z := by simpa [T.ValidArg1, T.dom1, hd, hle] using hv
                obtain ⟨n, rfl⟩ := IsN_exists_ofNat hn
                rw [fund1_P_of_Ω_le a0 a1 _ l hd hle]
                have hi := iteration_master a1 a0 l hle hd hg (fun t ht hv => ih1 t ha1 ht hv) n
                exact ⟨T.isNF1.p _ _ _ hi.2.1 T.isNF1.z hi.2.2.1 (T.Z_le _), hi.2.2.2⟩
              · have hi : T.index_Prop1 l z := by simpa [T.ValidArg1, T.dom1, hd, hle] using hv
                obtain ⟨hc, hs⟩ := ih1 z ha1 hz (by simpa [T.ValidArg1, hd] using hi)
                have hb := SDom_G1_lt_of_zero_support z _ a1 a0 hs hg (by
                  rw [index_Prop1_G1_empty l z hi a0 (by omega)]
                  intro x hx; cases hx)
                rw [fund1_P_of_Ω_gt a0 a1 z l hd hle]
                exact ⟨T.isNF1.p _ _ _ hc T.isNF1.z hb (T.Z_le _), SDom_wrap z _ a1 a0 hs⟩
      | P a20 a21 a22 =>
          obtain ⟨hc, hs⟩ := ih2 z ha2 hz hv
          exact ⟨T.isNF1.p _ _ _ ha1 hc hg (partial_order.trans _ _ _ (T.head_mono hs.1) hh),
            SDom_tail z _ _ a0 a1 hs⟩

theorem T.fund1_NF1_closed (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t) (hv : T.ValidArg1 s t) :
    T.isNF1 (T.fund1 s t) :=
  (master s t hs ht hv).1

def T.NF1 := { s : T // T.isNF1 s }

namespace Rank1Termination

def W : Nat → T → Prop
| u, a => ∀ X : T → Prop,
    (∀ b, T.index_Prop1 u b →
      (b = Z ∨
        ((T.dom1 b = .One ∨ T.dom1 b = .ω) ∧
          ∀ z, T.ValidArg1 b z → X (T.fund1 b z)) ∨
        (∃ m, ∃ _hm : m < u, T.dom1 b = .Ω m ∧
          ∀ z, T.ValidArg1 b z → W m z → X (T.fund1 b z))) → X b) → X a

def A (u : Nat) (X : T → Prop) (a : T) : Prop :=
  T.index_Prop1 u a ∧
    (a = Z ∨
      ((T.dom1 a = .One ∨ T.dom1 a = .ω) ∧
        ∀ z, T.ValidArg1 a z → X (T.fund1 a z)) ∨
      (∃ m, ∃ _hm : m < u, T.dom1 a = .Ω m ∧
        ∀ z, T.ValidArg1 a z → W m z → X (T.fund1 a z)))

theorem W_ind (u : Nat) (X : T → Prop) (h : ∀ a, A u X a → X a)
    (a : T) (ha : W u a) : X a := by
  unfold W at ha
  exact ha X (fun b hi hb => h b ⟨hi, hb⟩)

theorem A_mono (u : Nat) (X Y : T → Prop) (h : ∀ a, X a → Y a)
    (a : T) (ha : A u X a) : A u Y a := by
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with he | ⟨hd, hf⟩ | ⟨m, hm, hd, hf⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl ⟨hd, fun z hz => h _ (hf z hz)⟩)
  · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hw => h _ (hf z hz hw)⟩)

theorem W_intro (u : Nat) (a : T) (ha : A u (W u) a) : W u a := by
  unfold W
  intro X hX
  have hm := A_mono u (W u) X (fun b hb => W_ind u X
    (fun c hc => hX c hc.1 hc.2) b hb) a ha
  exact hX a hm.1 hm.2

theorem W_index (u : Nat) (a : T) (ha : W u a) : T.index_Prop1 u a :=
  W_ind u (T.index_Prop1 u) (fun _ h => h.1) a ha

theorem W_zero (u : Nat) : W u Z := W_intro u Z ⟨.z, Or.inl rfl⟩

theorem index_mono {u v : Nat} (huv : u ≤ v) (a : T)
    (ha : T.index_Prop1 u a) : T.index_Prop1 v a := by
  induction ha with
  | z => exact .z
  | p a0 a1 a2 hi _ ih => exact .p a0 a1 a2 (Nat.le_trans hi huv) ih

theorem A_level {u v : Nat} (huv : u ≤ v) (X : T → Prop) (a : T)
    (ha : A u X a) : A v X a := by
  refine ⟨index_mono huv a ha.1, ?_⟩
  rcases ha.2 with he | hn | ⟨m, hm, hd, hf⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr ⟨m, Nat.lt_of_lt_of_le hm huv, hd, hf⟩)

theorem W_mono {u v : Nat} (huv : u ≤ v) (a : T) (ha : W u a) : W v a :=
  W_ind u (W v) (fun b hb => W_intro v b (A_level huv (W v) b hb)) a ha

theorem W_nat (u : Nat) (a : T) (hi : T.index_Prop1 u a)
    (hd : T.dom1 a = .One ∨ T.dom1 a = .ω)
    (hf : ∀ z, T.ValidArg1 a z → W u (T.fund1 a z)) : W u a :=
  W_intro u a ⟨hi, Or.inr (Or.inl ⟨hd, hf⟩)⟩

theorem W_omega (u m : Nat) (hm : m < u) (a : T) (hi : T.index_Prop1 u a)
    (hd : T.dom1 a = .Ω m)
    (hf : ∀ z, T.ValidArg1 a z → W m z → W u (T.fund1 a z)) : W u a :=
  W_intro u a ⟨hi, Or.inr (Or.inr ⟨m, hm, hd, hf⟩)⟩

theorem index_add (u : Nat) (a b : T) (ha : T.index_Prop1 u a)
    (hb : T.index_Prop1 u b) : T.index_Prop1 u (T.add a b) := by
  induction ha with
  | z => exact hb
  | p a0 a1 a2 hi _ ih =>
    rw [T.P_add_eq]
    exact .p a0 a1 _ hi ih

theorem dom_add (a : T) (b0 : Nat) (b1 b2 : T) :
    T.dom1 (T.add a (P b0 b1 b2)) = T.dom1 (P b0 b1 b2) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih =>
      rw [T.P_add_eq]
      obtain ⟨c0, c1, c2, hc⟩ := T.exists_add_eq_P a2 b0 b1 b2
      rw [hc, dom1_P_tail, ← hc, ih]

theorem fund_add (a : T) (b0 : Nat) (b1 b2 z : T) :
    T.fund1 (T.add a (P b0 b1 b2)) z = T.add a (T.fund1 (P b0 b1 b2) z) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih =>
      obtain ⟨c0, c1, c2, hc⟩ := T.exists_add_eq_P a2 b0 b1 b2
      rw [T.P_add_eq, T.P_add_eq, hc, fund1_P_tail, ← hc, ih]

theorem A_add (u : Nat) (X : T → Prop) (a : T) (b0 : Nat) (b1 b2 : T)
    (ha : T.index_Prop1 u a) (hb : A u (fun b => X (T.add a b)) (P b0 b1 b2)) :
    A u X (T.add a (P b0 b1 b2)) := by
  refine ⟨index_add u a _ ha hb.1, ?_⟩
  rcases hb.2 with he | ⟨hd, hf⟩ | ⟨m, hm, hd, hf⟩
  · cases he
  · refine Or.inr (Or.inl ⟨by simpa [dom_add] using hd, ?_⟩)
    intro z hz
    rw [fund_add]
    exact hf z (by simpa [T.ValidArg1, dom_add] using hz)
  · refine Or.inr (Or.inr ⟨m, hm, by simpa [dom_add] using hd, ?_⟩)
    intro z hz hw
    rw [fund_add]
    exact hf z (by simpa [T.ValidArg1, dom_add] using hz) hw

theorem add_closed (u : Nat) (X : T → Prop) (hX : ∀ b, A u X b → X b)
    (a : T) (hi : T.index_Prop1 u a) (ha : X a) :
    ∀ b, A u (fun b => X (T.add a b)) b → X (T.add a b) := by
  intro b hb
  cases b with
  | Z => rw [T.add_Z]; exact ha
  | P b0 b1 b2 => exact hX _ (A_add u X a b0 b1 b2 hi hb)

theorem W_add (u : Nat) (a b : T) (ha : W u a) (hb : W u b) : W u (T.add a b) :=
  W_ind u (fun b => W u (T.add a b))
    (add_closed u (W u) (W_intro u) a (W_index u a ha) ha) b hb

theorem W_mul (u : Nat) (a : T) (ha : W u a) (n : T) (hn : T.IsN n) :
    W u (T.mul a n) := by
  induction hn with
  | zero => exact W_zero u
  | succ n _ ih => exact W_add u _ a ih ha

theorem W_base (u : Nat) : W u (P u Z Z) := by
  cases u with
  | zero =>
    exact W_nat 0 _ (.p 0 Z Z (Nat.le_refl 0) .z) (Or.inl rfl)
      (fun _ _ => W_zero 0)
  | succ u =>
    exact W_omega (u+1) u (Nat.lt_succ_self u) _ (.p _ Z Z (Nat.le_refl _) .z) rfl
      (fun z _ hz => W_mono (Nat.le_succ u) z hz)

theorem collapse_closed (v : Nat) :
    ∀ b, A v (fun b => ∀ q, q < v → W q (P q b Z)) b →
      ∀ q, q < v → W q (P q b Z) := by
  intro b hb q hq
  rcases hb.2 with rfl | ⟨hd | hd, hf⟩ | ⟨m, hm, hd, hf⟩
  · exact W_base q
  · apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z) (Or.inr (dom1_P_of_One q b hd))
    intro z hz
    rw [fund1_P_of_One q b z hd]
    exact W_mul q _ (hf Z (by simp [T.ValidArg1, hd]) q hq) z
      (by simpa [T.ValidArg1, T.dom1, hd] using hz)
  · apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z) (Or.inr (dom1_P_of_ω q b hd))
    intro z hz
    rw [fund1_P_of_ω q b z hd]
    exact hf z (by simpa [T.ValidArg1, T.dom1, hd] using hz) q hq
  · by_cases hqm : q ≤ m
    · apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z)
        (Or.inr (by simp [T.dom1, hd, hqm]))
      intro z hz
      have hn : T.IsN z := by simpa [T.ValidArg1, T.dom1, hd, hqm] using hz
      have hw : W m (T.iter (fun x => P m (T.fund1 b x) Z) z) := by
        clear hz
        induction hn with
        | zero => exact W_zero m
        | succ z _ ih => exact hf _ ((ValidArg1_Ω_iff b _ m hd).mpr (W_index m _ ih)) ih m hm
      rw [fund1_P_of_Ω_le q b z m hd hqm]
      exact hf _ ((ValidArg1_Ω_iff b _ m hd).mpr (W_index m _ hw)) hw q hq
    · apply W_omega q m (Nat.lt_of_not_le hqm) _ (.p _ _ _ (Nat.le_refl q) .z)
        (by simp [T.dom1, hd, hqm])
      intro z hz hw
      rw [fund1_P_of_Ω_gt q b z m hd hqm]
      exact hf z (by simpa [T.ValidArg1, T.dom1, hd, hqm] using hz) hw q hq

theorem add_assoc (a b c : T) : T.add (T.add a b) c = T.add a (T.add b c) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih => rw [T.P_add_eq, T.P_add_eq, T.P_add_eq, ih]

theorem append_collapse_closed (v : Nat) (X : T → Prop)
    (hi : ∀ a, X a → T.index_Prop1 v a) (hX : ∀ a, A v X a → X a) :
    ∀ b, A v (fun b => ∀ a, X a → X (T.add a (P v b Z))) b →
      ∀ a, X a → X (T.add a (P v b Z)) := by
  intro b hb a ha
  have hp (h : A v (fun b => X (T.add a b)) (P v b Z)) := hX _ (A_add v X a v b Z (hi a ha) h)
  have idx : T.index_Prop1 v (P v b Z) := .p _ _ _ (Nat.le_refl v) .z
  apply hp
  rcases hb.2 with rfl | ⟨hd | hd, hf⟩ | ⟨m, hm, hd, hf⟩
  · cases v with
    | zero => exact ⟨idx, Or.inr (Or.inl ⟨Or.inl rfl, fun _ _ => by
        simpa [T.fund1, T.dom1, T.add_Z] using ha⟩)⟩
    | succ v =>
        refine ⟨idx, Or.inr (Or.inr ⟨v, Nat.lt_succ_self v, rfl, ?_⟩)⟩
        intro z _ hz
        exact W_ind (v + 1) (fun z => X (T.add a z))
          (add_closed (v + 1) X hX a (hi a ha) ha) z (W_mono (Nat.le_succ v) z hz)
  · refine ⟨idx, Or.inr (Or.inl ⟨Or.inr (dom1_P_of_One v b hd), ?_⟩)⟩
    intro z hz
    rw [fund1_P_of_One v b z hd]
    have hn : T.IsN z := by simpa [T.ValidArg1, T.dom1, hd] using hz
    have hstep := hf Z (by simp [T.ValidArg1, hd])
    clear hz
    induction hn with
    | zero => simpa [T.mul, T.add_Z] using ha
    | succ z _ ih =>
        change X (T.add a (T.add _ _))
        rw [← add_assoc]
        exact hstep _ ih
  · refine ⟨idx, Or.inr (Or.inl ⟨Or.inr (dom1_P_of_ω v b hd), ?_⟩)⟩
    intro z hz
    rw [fund1_P_of_ω v b z hd]
    exact hf z (by simpa [T.ValidArg1, T.dom1, hd] using hz) a ha
  · have hn : ¬ v ≤ m := Nat.not_le_of_gt hm
    refine ⟨idx, Or.inr (Or.inr ⟨m, hm, by simp [T.dom1, hd, hn], ?_⟩)⟩
    intro z hz hw
    rw [fund1_P_of_Ω_gt v b z m hd hn]
    exact hf z (by simpa [T.ValidArg1, T.dom1, hd, hn] using hz) hw a ha

theorem exists_level (a : T) : ∃ v, ∀ u, v ≤ u → W u a := by
  induction a with
  | Z => exact ⟨0, fun u _ => W_zero u⟩
  | P a0 a1 a2 ih1 ih2 =>
      obtain ⟨v1, hv1⟩ := ih1
      obtain ⟨v2, hv2⟩ := ih2
      refine ⟨a0 + v1 + v2, ?_⟩
      intro u hu
      have ha0 : a0 ≤ u := by omega
      have ha1 := hv1 u (by omega)
      have hp : W u (P a0 a1 Z) := by
        rcases Nat.lt_or_eq_of_le ha0 with hlt | rfl
        · exact W_mono ha0 _ (W_ind u _ (collapse_closed u) a1 ha1 a0 hlt)
        · let X := fun b => W a0 b ∧ T.index_Prop1 a0 b
          have hX : ∀ b, A a0 X b → X b :=
            fun b hb => ⟨W_intro a0 b (A_mono a0 X (W a0) (fun _ h => h.1) b hb), hb.1⟩
          exact (W_ind a0 _ (append_collapse_closed a0 X (fun _ h => h.2) hX)
            a1 ha1 Z ⟨W_zero a0, .z⟩).1
      simpa [T.P_add_eq, T.add.eq_1] using W_add u _ a2 hp (hv2 u (by omega))

theorem W_all (u : Nat) (a : T) (hi : T.index_Prop1 u a) : W u a := by
  induction hi with
  | z => exact W_zero u
  | p a0 a1 a2 h0 _ ih =>
      obtain ⟨v, hv⟩ := exists_level a1
      have hs := W_ind (v + a0 + 1) _ (collapse_closed (v + a0 + 1))
        a1 (hv _ (by omega)) a0 (by omega)
      simpa [T.P_add_eq, T.add.eq_1] using W_add u _ a2 (W_mono h0 _ hs) ih

end Rank1Termination

theorem head_le_index (i j : Nat) (s t : T) (h : P i s Z ≤ P j t Z) : i ≤ j := by
  rcases h with h | h
  · cases h <;> omega
  · cases h; exact Nat.le_refl _

theorem dom1_Ω_head (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l) :
    ∃ i s t, a = P i s t ∧ l < i := by
  induction a with
  | Z => cases hd
  | P i s t _ iht =>
      obtain ⟨_, ht, _, hh⟩ := T.isNF1_P_inv i s t ha
      refine ⟨i, s, t, rfl, ?_⟩
      cases t with
      | Z =>
          cases he : T.dom1 s with
          | Zero => cases i <;> simp_all [T.dom1]
          | One | ω => simp [T.dom1, he] at hd
          | Ω m =>
              rw [dom1_P_of_Ω i s m he] at hd
              split at hd
              · cases hd
              · cases hd; omega
      | P j b c =>
          obtain ⟨j', b', c', he, hj⟩ := iht ht hd
          cases he
          exact Nat.lt_of_lt_of_le hj (head_le_index j i b s hh)

theorem fund1_Ω_arg_le (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l)
    (z : T) (hz : T.index_Prop1 l z) : z ≤ T.fund1 a z := by
  obtain ⟨i, s, t, rfl, hi⟩ := dom1_Ω_head a ha l hd
  have hsmall (b c : T) : z < P i b c := by
    cases hz with
    | z => exact .Z_lt_P _ _ _
    | p j x y hj _ => exact .p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hj hi)
  cases t with
  | P j b c => exact Or.inl (hsmall _ _)
  | Z =>
      cases hs : T.dom1 s with
      | Zero =>
          cases i with
          | zero => omega
          | succ i => rw [fund1_Psucc_of_Zero i s z hs]; exact Or.inr rfl
      | One | ω => simp [T.dom1, hs] at hd
      | Ω m =>
          by_cases him : i ≤ m
          · simp [T.dom1, hs, him] at hd
          · rw [fund1_P_of_Ω_gt i s z m hs him]; exact Or.inl (hsmall _ _)

def cutBound (l : Nat) (z : T) : T → Prop
| Z => Z < z
| P i s t => if i ≤ l then P i s t < z else cutBound l z s ∧ cutBound l z t

theorem cutBound_mono (l : Nat) (z w b : T) (hzw : z ≤ w) (hb : cutBound l z b) :
    cutBound l w b := by
  induction b with
  | Z => exact lt_of_lt_of_le_thm T _ _ _ hb hzw
  | P i s t ihs iht =>
      by_cases hi : i ≤ l <;> simp only [cutBound, hi, ite_true, ite_false] at hb ⊢
      · exact lt_of_lt_of_le_thm T _ _ _ hb hzw
      · exact ⟨ihs hb.1, iht hb.2⟩

theorem fund1_Ω_above (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l)
    (z : T) (hz : T.index_Prop1 l z) :
    ∀ b, T.isNF1 b → b < a → cutBound l z b → b < T.fund1 a z := by
  induction a with
  | Z => cases hd
  | P i s t ihs iht =>
      intro b hb hba hcut
      obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t ha
      cases b with
      | Z => exact lt_of_lt_of_le_thm T _ _ _ hcut (fund1_Ω_arg_le _ ha l hd z hz)
      | P j x y =>
          by_cases hj : j ≤ l
          · exact lt_of_lt_of_le_thm T _ _ _ (by simpa [cutBound, hj] using hcut)
              (fund1_Ω_arg_le _ ha l hd z hz)
          · simp only [cutBound, ite_eq_right hj] at hcut
            obtain ⟨hx, hy, _, _⟩ := T.isNF1_P_inv j x y hb
            cases t with
            | P t0 t1 t2 =>
                rw [fund1_P_tail]
                cases hba with
                | p_head _ _ _ _ _ _ h => exact .p_head _ _ _ _ _ _ h
                | p_mid _ _ _ _ _ h => exact .p_mid _ _ _ _ _ h
                | p_tail _ _ _ _ h => exact .p_tail _ _ _ _ (iht ht hd _ hy h hcut.2)
            | Z =>
                cases he : T.dom1 s with
                | Zero =>
                    have hsz := dom1_Zero_imp_eq_Z s he
                    subst s
                    cases i with
                    | zero => cases hd
                    | succ i =>
                        have heq : i = l := by simpa [T.dom1] using hd
                        subst i
                        cases hba with
                        | p_head _ _ _ _ _ _ h => exact False.elim (hj (Nat.le_of_lt_succ h))
                        | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
                | One | ω => simp [T.dom1, he] at hd
                | Ω m =>
                    by_cases him : i ≤ m
                    · simp [T.dom1, he, him] at hd
                    · have heq : m = l := by simpa [T.dom1, he, him] using hd
                      subst m
                      rw [fund1_P_of_Ω_gt i s z l he him]
                      cases hba with
                      | p_head _ _ _ _ _ _ h => exact .p_head _ _ _ _ _ _ h
                      | p_mid _ _ _ _ _ h => exact .p_mid _ _ _ _ _ (ihs hs he _ hx h hcut.1)
                      | p_tail _ _ _ _ h => cases h

theorem G1_size_lt (l : Nat) (b : T) : ∀ x ∈ T.G1 l b, x.size < b.size := by
  induction b with
  | Z => intro x hx; cases hx
  | P i s t ihs iht =>
      intro x hx
      by_cases hi : l ≤ i
      · simp [T.G1, hi] at hx
        rcases hx with rfl | hx | hx
        · exact T.size_lt_size_P_left _ _ _
        · exact Nat.lt_trans (ihs x hx) (T.size_lt_size_P_left _ _ _)
        · exact Nat.lt_trans (iht x hx) (T.size_lt_size_P_right _ _ _)
      · exact Nat.lt_trans (iht x (by simpa [T.G1, hi] using hx)) (T.size_lt_size_P_right _ _ _)

theorem iter_cutBound (a : T) (l : Nat) (hd : T.dom1 a = .Ω l)
    (b : T) (hb : T.isNF1 b)
    (happrox : ∀ x ∈ T.G1 l b, T.isNF1 x → (∀ y ∈ T.G1 l x, y < x) →
      ∃ n, x < T.fund1 a (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n))) :
    ∃ n, cutBound l (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n)) b := by
  have hmono (n m : Nat) (h : n < m) :=
    iter_F_strict_mono_ofNat a l hd (T.fund1_strict_mono_dec a) m n h
  induction b with
  | Z => exact ⟨1, T.Lt.Z_lt_P _ _ _⟩
  | P i s t ihs iht =>
      obtain ⟨hs, ht, hgs, _⟩ := T.isNF1_P_inv i s t hb
      rcases nat_lt_total i l with hil | hli | rfl
      · refine ⟨1, ?_⟩
        rw [cutBound, ite_eq_left (Nat.le_of_lt hil)]
        exact .p_head _ _ _ _ _ _ hil
      · have hin : ¬ i ≤ l := by omega
        have hli' := Nat.le_of_lt hli
        obtain ⟨n, hn⟩ := ihs hs (fun x hx => happrox x (by simp [T.G1, hli', hx]))
        obtain ⟨m, hm⟩ := iht ht (fun x hx => happrox x (by simp [T.G1, hli', hx]))
        refine ⟨n + m + 1, ?_⟩
        rw [cutBound, ite_eq_right hin]
        exact ⟨cutBound_mono l _ _ s (Or.inl (hmono n _ (by omega))) hn,
          cutBound_mono l _ _ t (Or.inl (hmono m _ (by omega))) hm⟩
      · obtain ⟨n, hn⟩ := happrox s (by simp [T.G1]) hs hgs
        refine ⟨n + 1, ?_⟩
        rw [cutBound, ite_eq_left (Nat.le_refl _)]
        exact .p_mid _ _ _ _ _ hn

theorem iteration_cofinal (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l) :
    ∀ b, T.isNF1 b → b < a → (∀ x ∈ T.G1 l b, x < b) →
      ∃ n, b < T.fund1 a (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n)) := by
  intro b
  induction b using (measure T.size).wf.induction with
  | h b ih =>
      intro hb hba hgb
      obtain ⟨m, hm⟩ := iter_cutBound a l hd b hb (fun x hx hnx hgx =>
        ih x (G1_size_lt l b x hx) hnx (lt_trans_thm _ _ _ (hgb x hx) hba) hgx)
      exact ⟨m, fund1_Ω_above a ha l hd _
        (iter_index_Prop1 l _ (fun z => ⟨T.fund1 a z, rfl⟩) (T.ofNat m)) b hb hba hm⟩

theorem dom1_One_PZ (i : Nat) (s : T) (hd : T.dom1 (P i s Z) = .One) :
    i = 0 ∧ s = Z := by
  cases hs : T.dom1 s with
  | Zero =>
      have he := dom1_Zero_imp_eq_Z s hs
      cases i <;> simp_all [T.dom1]
  | One | ω => simp [T.dom1, hs] at hd
  | Ω l =>
      rw [dom1_P_of_Ω i s l hs] at hd
      split at hd <;> cases hd

theorem fund1_One_const (a : T) (hd : T.dom1 a = .One) (z : T) :
    T.fund1 a z = T.fund1 a Z := by
  induction a with
  | Z => cases hd
  | P i s t _ iht =>
      cases t with
      | Z => obtain ⟨rfl, rfl⟩ := dom1_One_PZ i s hd; rfl
      | P j b c => rw [fund1_P_tail, fund1_P_tail, iht hd]

theorem fund1_One_upper (a : T) (hd : T.dom1 a = .One) :
    ∀ b, b < a → b ≤ T.fund1 a Z := by
  induction a with
  | Z => cases hd
  | P i s t _ iht =>
      intro b hba
      cases t with
      | Z =>
          obtain ⟨rfl, rfl⟩ := dom1_One_PZ i s hd
          cases hba with
          | Z_lt_P => exact Or.inr rfl
          | p_head _ _ _ _ _ _ h => omega
          | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
      | P j x y =>
          rw [fund1_P_tail]
          cases hba with
          | Z_lt_P => exact T.Z_le _
          | p_head _ _ _ _ _ _ h => exact Or.inl (.p_head _ _ _ _ _ _ h)
          | p_mid _ _ _ _ _ h => exact Or.inl (.p_mid _ _ _ _ _ h)
          | p_tail _ _ _ _ h =>
              rcases iht hd _ h with h | h
              · exact Or.inl (.p_tail _ _ _ _ h)
              · rw [h]; exact Or.inr rfl

theorem isNF1_index (l i : Nat) (s t : T) (ha : T.isNF1 (P i s t)) (hi : i ≤ l) :
    T.index_Prop1 l (P i s t) := by
  induction t generalizing i s with
  | Z => exact .p _ _ _ hi .z
  | P j b c _ ih =>
      obtain ⟨_, ht, _, hh⟩ := T.isNF1_P_inv i s _ ha
      exact .p _ _ _ hi (ih j b ht (Nat.le_trans (head_le_index j i b s hh) hi))

theorem one_le_P (i : Nat) (s : T) : P 0 Z Z ≤ P i s Z := by
  cases i with
  | zero =>
    cases s with
    | Z => exact Or.inr rfl
    | P j x y => exact Or.inl (.p_mid 0 Z _ Z Z (.Z_lt_P j x y))
  | succ i => exact Or.inl (.p_head 0 (i+1) Z s Z Z (Nat.zero_lt_succ i))

theorem isNF1_succ (a : T) (ha : T.isNF1 a) : T.isNF1 (T.add a (P 0 Z Z)) := by
  induction a with
  | Z => exact .p 0 Z Z .z .z (fun _ h => by cases h) (T.Z_le _)
  | P i s t _ iht =>
      obtain ⟨hs, ht, hg, hh⟩ := T.isNF1_P_inv i s t ha
      rw [T.P_add_eq]
      refine .p _ _ _ hs (iht ht) hg ?_
      cases t with
      | Z => exact one_le_P i s
      | P j x y => rw [T.P_add_eq]; exact hh

theorem cutBound_exists (l : Nat) (b : T) (hb : T.isNF1 b) :
    ∃ z, T.isNF1 z ∧ T.index_Prop1 l z ∧ cutBound l z b := by
  induction b with
  | Z => exact ⟨P 0 Z Z, isNF1_succ Z .z, .p 0 Z Z (Nat.zero_le l) .z, .Z_lt_P _ _ _⟩
  | P i s t ihs iht =>
      obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t hb
      by_cases hi : i ≤ l
      · refine ⟨T.add (P i s t) (P 0 Z Z), isNF1_succ _ hb,
          Rank1Termination.index_add l _ _ (isNF1_index l i s t hb hi)
            (.p 0 Z Z (Nat.zero_le l) .z), ?_⟩
        rw [cutBound, ite_eq_left hi]
        exact add_lt_add_of_ne_Z _ _ (fun h => by cases h)
      · obtain ⟨z, hz, hiz, hsz⟩ := ihs hs
        obtain ⟨w, hw, hiw, htw⟩ := iht ht
        rcases linear_order.total z w with hzw | hwz
        · refine ⟨w, hw, hiw, ?_⟩
          rw [cutBound, ite_eq_right hi]
          exact ⟨cutBound_mono l z w s hzw hsz, htw⟩
        · refine ⟨z, hz, hiz, ?_⟩
          rw [cutBound, ite_eq_right hi]
          exact ⟨hsz, cutBound_mono l w z t hwz htw⟩

theorem mul_cofinal (i : Nat) (s : T) (b : T) (hb : T.isNF1 b)
    (hh : T.head b ≤ P i s Z) : ∃ n, b < T.mul (P i s Z) (T.ofNat n) := by
  induction b with
  | Z => exact ⟨1, T.Lt.Z_lt_P _ _ _⟩
  | P j x y _ ih =>
      obtain ⟨_, hy, _, hhy⟩ := T.isNF1_P_inv j x y hb
      rcases hh with hh | hh
      · cases hh with
        | p_head _ _ _ _ _ _ h => exact ⟨1, .p_head _ _ _ _ _ _ h⟩
        | p_mid _ _ _ _ _ h => exact ⟨1, .p_mid _ _ _ _ _ h⟩
        | p_tail _ _ _ _ h => cases h
      · cases hh
        obtain ⟨n, hn⟩ := ih hy hhy
        exact ⟨n + 1, by rw [mul_succ_shape]; exact .p_tail _ _ _ _ hn⟩

theorem fund1_ω_cofinal (a : T) (ha : T.isNF1 a) (hd : T.dom1 a = .ω) :
    ∀ b, T.isNF1 b → b < a → ∃ n, b < T.fund1 a (T.ofNat n) := by
  induction a with
  | Z => cases hd
  | P i s t ihs iht =>
      intro b hb hba
      obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t ha
      cases b with
      | Z =>
          refine ⟨1, lt_of_le_of_lt_thm T Z (T.fund1 (P i s t) Z) _ (T.Z_le _) ?_⟩
          exact T.fund1_strict_mono_dec _ Z (T.ofNat 1) (.Z_lt_P _ _ _)
            ((ValidArg1_ω_iff _ Z hd).mpr .zero)
            ((ValidArg1_ω_iff _ (T.ofNat 1) hd).mpr (ofNat_IsN 1))
      | P j x y =>
          obtain ⟨hx, hy, hgx, _⟩ := T.isNF1_P_inv j x y hb
          cases t with
          | P k c d =>
              cases hba with
              | p_head _ _ _ _ _ _ h => exact ⟨0, .p_head _ _ _ _ _ _ h⟩
              | p_mid _ _ _ _ _ h => exact ⟨0, .p_mid _ _ _ _ _ h⟩
              | p_tail _ _ _ _ h =>
                  obtain ⟨n, hn⟩ := iht ht hd _ hy h
                  exact ⟨n, .p_tail _ _ _ _ hn⟩
          | Z =>
              cases he : T.dom1 s with
              | Zero => cases i <;> simp [T.dom1, he] at hd
              | One =>
                  cases hba with
                  | p_head _ _ _ _ _ _ h =>
                      exact ⟨1, by rw [fund1_P_of_One i s _ he]; exact .p_head _ _ _ _ _ _ h⟩
                  | p_mid _ _ _ _ _ h =>
                      rcases fund1_One_upper s he _ h with hxp | hxp
                      · exact ⟨1, by rw [fund1_P_of_One i s _ he]; exact .p_mid _ _ _ _ _ hxp⟩
                      · obtain ⟨n, hn⟩ := mul_cofinal i (T.fund1 s Z) _ hb (by rw [hxp]; exact Or.inr rfl)
                        exact ⟨n, by rw [fund1_P_of_One i s _ he]; exact hn⟩
                  | p_tail _ _ _ _ h => cases h
              | ω =>
                  cases hba with
                  | p_head _ _ _ _ _ _ h =>
                      exact ⟨0, by rw [fund1_P_of_ω i s _ he]; exact .p_head _ _ _ _ _ _ h⟩
                  | p_mid _ _ _ _ _ h =>
                      obtain ⟨n, hn⟩ := ihs hs he _ hx h
                      exact ⟨n, by rw [fund1_P_of_ω i s _ he]; exact .p_mid _ _ _ _ _ hn⟩
                  | p_tail _ _ _ _ h => cases h
              | Ω l =>
                  have hil : i ≤ l := by simpa [T.dom1, he] using hd
                  cases hba with
                  | p_head _ _ _ _ _ _ h =>
                      exact ⟨0, by rw [fund1_P_of_Ω_le i s _ l he hil]; exact .p_head _ _ _ _ _ _ h⟩
                  | p_mid _ _ _ _ _ h =>
                      obtain ⟨n, hn⟩ := iteration_cofinal s hs l he _ hx h
                        (fun z hz => hgx z (G1_antitone i l hil _ z hz))
                      exact ⟨n, by rw [fund1_P_of_Ω_le i s _ l he hil]; exact .p_mid _ _ _ _ _ hn⟩
                  | p_tail _ _ _ _ h => cases h

theorem IsN_isNF1 (a : T) (ha : T.IsN a) : T.isNF1 a := by
  induction ha with
  | zero => exact .z
  | succ a hn ih =>
    refine .p 0 Z a .z ih (fun _ h => by cases h) ?_
    cases hn with
    | zero => exact T.Z_le _
    | succ a _ => exact Or.inr rfl

theorem fund1_cofinal (a b : T) (ha : T.isNF1 a) (hb : T.isNF1 b) (hba : b < a) :
    ∃ z, T.isNF1 z ∧ T.ValidArg1 a z ∧ b ≤ T.fund1 a z := by
  cases hd : T.dom1 a with
  | Zero => rw [dom1_Zero_imp_eq_Z a hd] at hba; cases hba
  | One => exact ⟨Z, .z, (ValidArg1_One_iff a Z hd).mpr rfl, fund1_One_upper a hd b hba⟩
  | ω =>
      obtain ⟨n, hn⟩ := fund1_ω_cofinal a ha hd b hb hba
      exact ⟨T.ofNat n, IsN_isNF1 _ (ofNat_IsN n),
        (ValidArg1_ω_iff a _ hd).mpr (ofNat_IsN n), Or.inl hn⟩
  | Ω l =>
      obtain ⟨z, hz, hi, hc⟩ := cutBound_exists l b hb
      exact ⟨z, hz, (ValidArg1_Ω_iff a z l hd).mpr hi,
        Or.inl (fund1_Ω_above a ha l hd z hi b hb hba hc)⟩

theorem NF1_acc_of_le (a b : T.NF1)
    (ha : Acc (fun x y : T.NF1 => x.1 < y.1) a) (hba : b.1 ≤ a.1) :
    Acc (fun x y : T.NF1 => x.1 < y.1) b := by
  rcases hba with h | h
  · exact ha.inv h
  · cases Subtype.ext h; exact ha

theorem T.well_founded_NF1 : WellFounded (fun s t : T.NF1 => s.1 < t.1) := by
  constructor
  intro a
  obtain ⟨u, hu⟩ := Rank1Termination.exists_level a.1
  apply Rank1Termination.W_ind u
    (fun b => ∀ hb : T.isNF1 b, Acc (fun s t : T.NF1 => s.1 < t.1) ⟨b, hb⟩)
    ?_ a.1 (hu u (Nat.le_refl u)) a.2
  intro b hg hb
  constructor
  intro c hcb
  obtain ⟨z, hz, hv, hle⟩ := fund1_cofinal b c.1 hb c.2 hcb
  have hnf := T.fund1_NF1_closed b z hb hz hv
  apply NF1_acc_of_le ⟨T.fund1 b z, hnf⟩ c ?_ hle
  rcases hg.2 with rfl | ⟨_, hf⟩ | ⟨m, _, hd, hf⟩
  · exact False.elim (lt_Z_inv hcb)
  · exact hf z hv hnf
  · exact hf z hv (Rank1Termination.W_all m z ((ValidArg1_Ω_iff b z m hd).mp hv)) hnf

def T.LF1 (n : Nat) := P 0 (P n Z Z) Z

inductive T.isOT1 : T → Prop where
| base (n : Nat) : T.isOT1 (T.LF1 n)
| step (s : T) (hs : T.isOT1 s) (n : Nat) : T.isOT1 (T.fund1 s (T.ofNat n))

theorem dom1_Ω_not_countable (a : T) (ha : T.isNF1 a) (hc : a < P 1 Z Z)
    (l : Nat) : T.dom1 a ≠ .Ω l := by
  intro hd
  obtain ⟨i, s, t, rfl, hi⟩ := dom1_Ω_head a ha l hd
  cases hc with
  | p_head _ _ _ _ _ _ h => omega
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

theorem LF1_isNF1 (n : Nat) : T.isNF1 (T.LF1 n) := by
  refine .p _ _ _ (.p _ _ _ .z .z (by simp [T.G1]) (T.Z_le _)) .z ?_ (T.Z_le _)
  simpa [T.G1] using (show Z < P n Z Z from .Z_lt_P n Z Z)

theorem isOT1_sound (a : T) (ha : T.isOT1 a) : T.isNF1 a ∧ a < P 1 Z Z := by
  induction ha with
  | base n => exact ⟨LF1_isNF1 n, .p_head 0 1 _ Z Z Z (Nat.zero_lt_succ 0)⟩
  | step a _ n ih =>
      have step (x) (hx : T.isNF1 x) (hv : T.ValidArg1 a x) :=
        And.intro (T.fund1_NF1_closed a x ih.1 hx hv) (lt_trans_thm _ _ _ (T.fund1_fall a x hv) ih.2)
      cases hd : T.dom1 a with
      | Zero => rw [dom1_Zero_imp_eq_Z a hd, T.fund1.eq_1]; exact ⟨.z, .Z_lt_P 1 Z Z⟩
      | One =>
          rw [fund1_One_const a hd (T.ofNat n)]
          exact step Z .z ((ValidArg1_One_iff a Z hd).mpr rfl)
      | ω => exact step _ (IsN_isNF1 _ (ofNat_IsN n)) ((ValidArg1_ω_iff a _ hd).mpr (ofNat_IsN n))
      | Ω l => exact False.elim (dom1_Ω_not_countable a ih.1 ih.2 l hd)

theorem fund1_countable_cofinal (a b : T) (ha : T.isNF1 a) (hb : T.isNF1 b)
    (hc : a < P 1 Z Z) (hba : b < a) :
    ∃ n, T.fund1 a (T.ofNat n) < a ∧ b ≤ T.fund1 a (T.ofNat n) := by
  cases hd : T.dom1 a with
  | Zero => rw [dom1_Zero_imp_eq_Z a hd] at hba; cases hba
  | One => exact ⟨0, T.fund1_fall a Z ((ValidArg1_One_iff a Z hd).mpr rfl), fund1_One_upper a hd b hba⟩
  | ω =>
      obtain ⟨n, hn⟩ := fund1_ω_cofinal a ha hd b hb hba
      exact ⟨n, T.fund1_fall a _ ((ValidArg1_ω_iff a _ hd).mpr (ofNat_IsN n)), Or.inl hn⟩
  | Ω l => exact False.elim (dom1_Ω_not_countable a ha hc l hd)

theorem isOT1_downward (a b : T) (ha : T.isOT1 a) (hb : T.isNF1 b) (hba : b ≤ a) :
    T.isOT1 b := by
  have main : ∀ a : T.NF1, T.isOT1 a.1 → ∀ b, T.isNF1 b → b ≤ a.1 → T.isOT1 b := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
        intro ha b hb hba
        rcases hba with hba | rfl
        · obtain ⟨n, hfall, hbound⟩ := fund1_countable_cofinal a.1 b a.2 hb (isOT1_sound a.1 ha).2 hba
          have hn := T.isOT1.step a.1 ha n
          exact ih ⟨_, (isOT1_sound _ hn).1⟩ hfall hn b hb hbound
        · exact ha
  exact main ⟨a, (isOT1_sound a ha).1⟩ ha b hb hba

theorem LF1_cofinal (a : T) (hc : a < P 1 Z Z) : ∃ n, a < T.LF1 n := by
  cases hc with
  | Z_lt_P => exact ⟨0, .Z_lt_P _ _ _⟩
  | p_head i _ s _ t _ hi =>
      have he : i = 0 := by omega
      subst i
      cases s with
      | Z => exact ⟨0, .p_mid _ _ _ _ _ (.Z_lt_P _ _ _)⟩
      | P j x y => exact ⟨j + 1, .p_mid _ _ _ _ _ (.p_head _ _ _ _ _ _ (Nat.lt_succ_self j))⟩
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

theorem T.isOT1_iff_isNF1 (s : T) : T.isOT1 s ↔ (T.isNF1 s ∧ s < P 1 Z Z) := by
  refine ⟨isOT1_sound s, ?_⟩
  intro hs
  obtain ⟨n, hn⟩ := LF1_cofinal s hs.2
  exact isOT1_downward _ s (.base n) hs.1 (Or.inl hn)

def T.OT1 := { s : T // T.isOT1 s }

theorem T.well_founded_OT1 : WellFounded (fun s t : T.OT1 => s.1 < t.1) := by
  exact InvImage.wf (fun s : T.OT1 => (⟨s.1, (isOT1_sound s.1 s.2).1⟩ : T.NF1)) T.well_founded_NF1

def T.OT1Step (a b : T.OT1) : Prop :=
  b.val ≠ T.Z ∧ ∃ n : Nat, a.val = T.fund1 b.val (T.ofNat n)

abbrev T.OT1FundLt : T.OT1 → T.OT1 → Prop :=
  FundOrder.TransClosure T.OT1Step

theorem T.OT1Step_lt {a b : T.OT1} (h : T.OT1Step a b) :
    a.val < b.val := by
  rcases h with ⟨hbne, n, ha⟩
  rw [ha]
  have hb := isOT1_sound b.val b.property
  cases hd : T.dom1 b.val with
  | Zero => exact False.elim (hbne (dom1_Zero_imp_eq_Z b.val hd))
  | One =>
      rw [fund1_One_const b.val hd (T.ofNat n)]
      exact T.fund1_fall b.val T.Z
        ((ValidArg1_One_iff b.val T.Z hd).mpr rfl)
  | ω =>
      exact T.fund1_fall b.val (T.ofNat n)
        ((ValidArg1_ω_iff b.val (T.ofNat n) hd).mpr (ofNat_IsN n))
  | Ω l =>
      exact False.elim (dom1_Ω_not_countable b.val hb.1 hb.2 l hd)

theorem T.OT1FundLt_lt {a b : T.OT1} (h : T.OT1FundLt a b) :
    a.val < b.val := by
  induction h with
  | single hstep => exact T.OT1Step_lt hstep
  | tail _ hstep ih =>
      exact strict_partial_order.trans _ _ _ ih (T.OT1Step_lt hstep)

theorem T.OT1FundLt_of_lt (a b : T.OT1) (hab : a.val < b.val) :
    T.OT1FundLt a b := by
  induction b using T.well_founded_OT1.induction generalizing a with
  | h b ih =>
      have hb := isOT1_sound b.val b.property
      have ha := isOT1_sound a.val a.property
      obtain ⟨n, hfall, hupper⟩ :=
        fund1_countable_cofinal b.val a.val hb.1 ha.1 hb.2 hab
      let c : T.OT1 :=
        ⟨T.fund1 b.val (T.ofNat n), T.isOT1.step b.val b.property n⟩
      have hbne : b.val ≠ T.Z := by
        intro hbz
        rw [hbz] at hab
        exact lt_Z_inv hab
      have hstep : T.OT1Step c b := by
        exact ⟨hbne, n, rfl⟩
      rcases hupper with hlt | heq
      · exact FundOrder.TransClosure.tail (ih c hfall a hlt) hstep
      · have hac : a = c := Subtype.ext heq
        subst a
        exact FundOrder.TransClosure.single hstep

theorem T.OT1FundLt_iff_lt (a b : T.OT1) :
    T.OT1FundLt a b ↔ a.val < b.val := by
  exact ⟨T.OT1FundLt_lt, T.OT1FundLt_of_lt a b⟩
