import Mbekworm.Sequence.generalizedBek
import Mbekworm.Sequence.mbekwarmDef
import Mbekworm.Buchholz.Rank1

open T

/-- The rank-one term specified for the ordinal notation `φ(n, 0, 0)`. -/
def T.phi000 (n : Nat) : T :=
  P 0 (P 1 (T.mul (P 1 (P 1 Z Z) Z) (T.ofNat n)) Z) Z

theorem T.phi000_zero : T.phi000 0 = P 0 (P 1 Z Z) Z := rfl

theorem T.phi000_zero_isNF1 : T.isNF1 (T.phi000 0) := by
  rw [T.phi000_zero]
  exact LF1_isNF1 1

/-- A lightweight strict-order isomorphism, independent of `mathlib`. -/
structure StrictOrderIso (A B : Type) [LT A] [LT B] where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  lt_iff_lt : ∀ a b, toFun a < toFun b ↔ a < b

theorem Acc.mapRelation {A : Sort u} {r s : A → A → Prop}
    (hsub : ∀ a b, s a b → r a b) :
    ∀ a, Acc r a → Acc s a := by
  intro a ha
  exact ha.recOn (motive := fun a _ => Acc s a)
    (fun a _ ih => Acc.intro a (fun b hba => ih b (hsub b a hba)))

/-- The `n = 0` normal forms over `Nat`. -/
def NatNF0 := {xs : List Nat // NF Nat 0 xs}

instance : LT NatNF0 where
  lt a b := a.val < b.val

/-- Cantor-normal-form lists, represented inside the rank-one Buchholz terms. -/
def T.cantorSeq : List Nat → T
  | [] => Z
  | n :: ns => P 0 (T.ofNat n) (T.cantorSeq ns)

theorem T.ofNat_injective : Function.Injective T.ofNat := by
  intro m n h
  rcases nat_lt_total m n with hmn | hnm | rfl
  · exact False.elim (lt_irrefl_thm _ (h ▸ ofNat_strict_mono hmn))
  · exact False.elim (lt_irrefl_thm _ (h ▸ ofNat_strict_mono hnm))
  · rfl

theorem T.cantorSeq_injective : Function.Injective T.cantorSeq := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => cases h
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          simp only [T.cantorSeq] at h
          have hmid : T.ofNat x = T.ofNat y := (T.P.inj h).2.1
          have htail : T.cantorSeq xs = T.cantorSeq ys := (T.P.inj h).2.2
          have hxy : x = y := T.ofNat_injective hmid
          subst y
          exact congrArg (List.cons x) (ih htail)

theorem T.cantorSeq_lt_iff (xs ys : List Nat) :
    T.cantorSeq xs < T.cantorSeq ys ↔ xs < ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil => cases h
        | cons y ys => exact List.Lex.nil
    | cons x xs ih =>
        cases ys with
        | nil => cases h
        | cons y ys =>
            rcases lt_inv 0 (T.ofNat x) (T.cantorSeq xs)
                0 (T.ofNat y) (T.cantorSeq ys) h with
              hzero | ⟨_, hmid⟩ | ⟨_, hmid, htail⟩
            · omega
            · exact List.Lex.rel (ofNat_reflect_lt hmid)
            · have hxy : x = y := T.ofNat_injective hmid
              subst y
              exact List.Lex.cons (ih ys htail)
  · intro h
    induction h with
    | nil => exact T.Lt.Z_lt_P _ _ _
    | rel hxy =>
        exact T.Lt.p_mid 0 (T.ofNat _) (T.ofNat _) _ _
          (ofNat_strict_mono hxy)
    | cons hxy ih =>
        exact T.Lt.p_tail 0 (T.ofNat _) _ _ ih

theorem T.cantorSeq_le_iff (xs ys : List Nat) :
    T.cantorSeq xs ≤ T.cantorSeq ys ↔ xs < ys ∨ xs = ys := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((T.cantorSeq_lt_iff xs ys).mp h)
    · exact Or.inr (T.cantorSeq_injective h)
  · rintro (h | rfl)
    · exact Or.inl ((T.cantorSeq_lt_iff xs ys).mpr h)
    · exact Or.inr rfl

theorem T.ofNat_lt_P1 (n : Nat) : T.ofNat n < P 1 Z Z := by
  cases n with
  | zero => exact T.Lt.Z_lt_P _ _ _
  | succ n => exact T.Lt.p_head 0 1 Z Z (T.ofNat n) Z (by omega)

theorem T.cantorSeq_lt_phi000_zero (xs : List Nat) :
    T.cantorSeq xs < T.phi000 0 := by
  cases xs with
  | nil => exact T.Lt.Z_lt_P _ _ _
  | cons n ns =>
      rw [T.phi000_zero]
      exact T.Lt.p_mid 0 (T.ofNat n) (P 1 Z Z) (T.cantorSeq ns) Z
        (T.ofNat_lt_P1 n)

theorem List.max?_append_singleton_nat (xs : List Nat) (a b : Nat)
    (h : xs.max? = some a) : (xs ++ [b]).max? = some (max a b) := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
      simp only [List.max?] at h ⊢
      injection h with h
      change some (List.foldl max x (xs ++ [b])) = some (max a b)
      rw [List.foldl_append]
      simp [h]

theorem List.max?_range_succ (m : Nat) :
    (List.range (m + 1)).max? = some m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, List.range_succ]
      rw [List.max?_append_singleton_nat _ m (m + 1) ih]
      simp

theorem parent_zero_append (l : List Nat) (v : Nat) :
    parent (l ++ [v]) 0 = some l.length := by
  simp [parent, parent_cand, List.max?_range_succ]

theorem parent_zero_cons (a : Nat) (l : List Nat) :
    parent (a :: l) 0 = some l.length := by
  simp [parent, parent_cand, List.max?_range_succ]

theorem true_parent_scan_empty_zero (list : List Nat) (pm : Nat)
    (hp : parent list #[].size = some pm) :
    true_parent_scan list pm #[] hp 0 (by simp) = none := by
  rfl

theorem true_parent_go_zero_singleton (k : Nat) :
    true_parent_go 0 [k + 1] (k + 1) #[] (by simp) = none := by
  rw [true_parent_go]
  simp only [Array.size_empty]
  split
  · rename_i hp
    rw [parent_zero_cons] at hp
  · rename_i pm hp
    have hpm : pm = 0 :=
      Option.some.inj (hp.symm.trans (parent_zero_cons (k + 1) []))
    subst pm
    simp [true_parent_scan_empty_zero, relatives]

theorem true_parent_go_zero_cons_append (a : Nat) (l : List Nat) (k : Nat) :
    true_parent_go 0 ((a :: l) ++ [k + 1]) (k + 1) #[] (by simp) =
      some l.length := by
  rw [true_parent_go]
  simp only [Array.size_empty]
  split
  · rename_i hp
    rw [parent_zero_append] at hp
    cases hp
  · rename_i pm hp
    have hpm : pm = (a :: l).length :=
      Option.some.inj (hp.symm.trans (parent_zero_append (a :: l) (k + 1)))
    subst pm
    have hget :
        ((a :: l) ++ [k + 1])[(a :: l).length]'(parent_lt_length _ 0 _ hp) =
          k + 1 := by
      simp
    rw [hget]
    split
    · rename_i hlt
      omega
    · simp only [Nat.zero_sub, Nat.min_self]
      rw [true_parent_scan_empty_zero]
      simp only [Nat.lt_irrefl, dite_false]
      rfl

theorem expand_zero_zero_last (l : List Nat) (n : Nat) :
    expand 0 (l ++ [0]) n = l := by
  simp [expand]

theorem expand_zero_succ_last (l : List Nat) (k n : Nat) :
    expand 0 (l ++ [k + 1]) n = l ++ List.replicate (n + 1) k := by
  cases l with
  | nil =>
      simp [expand, true_parent_go_zero_singleton, List.repeat]
  | cons a l =>
      have hlast : ((a :: l) ++ [k + 1]).getLast? = some (k + 1) :=
        List.getLast?_eq_some_iff.mpr ⟨a :: l, rfl⟩
      rw [expand, hlast]
      simp only [List.dropLast_append]
      rw [true_parent_go_zero_cons_append]
      simp [List.repeat, List.replicate_succ]

theorem pairwise_desc_append_replicate (l : List Nat) (k n : Nat)
    (h : List.Pairwise (fun x y : Nat => y < x ∨ y = x) (l ++ [k + 1])) :
    List.Pairwise (fun x y : Nat => y < x ∨ y = x)
      (l ++ List.replicate (n + 1) k) := by
  have hparts := List.pairwise_append.mp h
  apply List.pairwise_append.mpr
  refine ⟨hparts.1, List.pairwise_replicate.mpr (Or.inr (Or.inr rfl)), ?_⟩
  intro a ha b hb
  have hak := hparts.2.2 a ha (k + 1) (by simp)
  have hbk : b = k := by simpa using hb
  subst b
  rcases hak with hak | rfl
  · exact Or.inl (Nat.lt_trans (Nat.lt_succ_self k) hak)
  · exact Or.inl (Nat.lt_succ_self k)

theorem expand_zero_preserves_NF (xs : List Nat) (n : Nat)
    (h : NF Nat 0 xs) : NF Nat 0 (expand 0 xs n) := by
  cases hx : xs.getLast? with
  | none =>
      have hnil : xs = [] := List.getLast?_eq_none_iff.mp hx
      subst xs
      simp [expand, NF]
  | some last =>
      obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.mp hx
      cases last with
      | zero =>
          rw [expand_zero_zero_last]
          change List.Pairwise (fun x y : Nat => y < x ∨ y = x) l
          exact (List.pairwise_append.mp h).1
      | succ k =>
          rw [expand_zero_succ_last]
          exact pairwise_desc_append_replicate l k n h

theorem isOT_zero_NF (xs : List Nat) (h : isOT 0 xs) : NF Nat 0 xs := by
  induction h with
  | base n => simp [NF]
  | step s _ n ih => exact expand_zero_preserves_NF s n ih

def MbekOT0 := {xs : List Nat // isOT 0 xs}

instance : LT MbekOT0 where
  lt a b := a.val < b.val

def MbekOT0.toNatNF0 (a : MbekOT0) : NatNF0 :=
  ⟨a.val, isOT_zero_NF a.val a.property⟩

theorem MbekOT0.toNatNF0_lt_iff (a b : MbekOT0) :
    a.toNatNF0.val < b.toNatNF0.val ↔ a.val < b.val := Iff.rfl

theorem T.G1_ofNat_lt (n : Nat) :
    ∀ x ∈ T.G1 0 (T.ofNat n), x < T.ofNat n := by
  induction n with
  | zero => simp [T.ofNat, T.G1]
  | succ n ih =>
      intro x hx
      simp only [T.ofNat, T.G1, Nat.zero_le, ite_true,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx
      · exact T.Lt.Z_lt_P _ _ _
      · exact lt_trans_thm _ _ _ (ih x hx) (ofNat_one_step n)

theorem T.cantorSeq_isNF1 :
    ∀ xs : List Nat, NF Nat 0 xs → T.isNF1 (T.cantorSeq xs) := by
  intro xs
  induction xs with
  | nil =>
      intro _
      exact T.isNF1.z
  | cons n ns ih =>
      intro hnf
      change List.Pairwise (fun x y : Nat => y < x ∨ y = x) (n :: ns) at hnf
      have hrel := (List.pairwise_cons.mp hnf).1
      have htail := (List.pairwise_cons.mp hnf).2
      refine T.isNF1.p 0 (T.ofNat n) (T.cantorSeq ns)
        (IsN_isNF1 _ (ofNat_IsN n)) (ih htail) (T.G1_ofNat_lt n) ?_
      cases ns with
      | nil => exact T.Z_le _
      | cons m ms =>
          change T.P 0 (T.ofNat m) T.Z ≤ T.P 0 (T.ofNat n) T.Z
          rcases hrel m List.mem_cons_self with hmn | rfl
          · exact Or.inl (T.Lt.p_mid 0 (T.ofNat m) (T.ofNat n) Z Z
              (ofNat_strict_mono hmn))
          · exact Or.inr rfl

def NatNF0.toNF1 (a : NatNF0) : T.NF1 :=
  ⟨T.cantorSeq a.val, T.cantorSeq_isNF1 a.val a.property⟩

theorem NatNF0.toNF1_lt_iff (a b : NatNF0) :
    a.toNF1.val < b.toNF1.val ↔ a.val < b.val :=
  T.cantorSeq_lt_iff a.val b.val

theorem NatNF0.toNF1_lt_phi000_zero (a : NatNF0) :
    a.toNF1.val < T.phi000 0 :=
  T.cantorSeq_lt_phi000_zero a.val

/-- The direct constructive embedding of the `expand` system at `M = 0`
into rank-one normal forms. -/
def MbekOT0.toNF1 (a : MbekOT0) : T.NF1 :=
  a.toNatNF0.toNF1

theorem MbekOT0.toNF1_lt_iff (a b : MbekOT0) :
    a.toNF1.val < b.toNF1.val ↔ a.val < b.val :=
  T.cantorSeq_lt_iff a.val b.val

theorem MbekOT0.toNF1_lt_phi000_zero (a : MbekOT0) :
    a.toNF1.val < T.phi000 0 :=
  T.cantorSeq_lt_phi000_zero a.val

/-- The constructive image of `NatNF0.toNF1`; the preimage is retained as data,
so no choice principle is needed to define the inverse. -/
structure T.CantorNF1Image where
  term : T.NF1
  preimage : NatNF0
  term_eq : term = preimage.toNF1

instance : LT T.CantorNF1Image where
  lt a b := a.term.val < b.term.val

def NatNF0.toCantorImage (a : NatNF0) : T.CantorNF1Image :=
  ⟨a.toNF1, a, rfl⟩

def T.CantorNF1Image.toNatNF0 (a : T.CantorNF1Image) : NatNF0 :=
  a.preimage

def NatNF0.cantorImageIso : StrictOrderIso NatNF0 T.CantorNF1Image where
  toFun := NatNF0.toCantorImage
  invFun := T.CantorNF1Image.toNatNF0
  left_inv _ := rfl
  right_inv a := by
    cases a with
    | mk term preimage term_eq =>
        cases term_eq
        rfl
  lt_iff_lt a b := NatNF0.toNF1_lt_iff a b

theorem NatNF0.wellFounded :
    WellFounded (fun a b : NatNF0 => a.val < b.val) := by
  have hInv : WellFounded (InvImage (fun a b : T.NF1 => a.val < b.val) NatNF0.toNF1) :=
    InvImage.wf NatNF0.toNF1 T.well_founded_NF1
  constructor
  intro a
  exact Acc.mapRelation
    (fun b a hba => (NatNF0.toNF1_lt_iff b a).mpr hba)
    a (hInv.apply a)

theorem MbekOT0.wellFounded :
    WellFounded (fun a b : MbekOT0 => a.val < b.val) := by
  have hInv : WellFounded
      (InvImage (fun a b : NatNF0 => a.val < b.val) MbekOT0.toNatNF0) :=
    InvImage.wf MbekOT0.toNatNF0 NatNF0.wellFounded
  constructor
  intro a
  exact Acc.mapRelation
    (fun b a hba => (MbekOT0.toNatNF0_lt_iff b a).mpr hba)
    a (hInv.apply a)
