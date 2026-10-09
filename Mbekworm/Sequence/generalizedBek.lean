import Mbekworm.Sequence.order

instance (A : Type) [LT A] [DecidableLT A] : Min A where
  min a b := if a < b then a else b

def splitOn (A : Type) [DecidableEq A] (a : A) : List A → List (List A)
| [] => [[]]
| x :: xs =>
  if x = a then
    [] :: splitOn A a xs
  else
    match splitOn A a xs with
    | [] => [[x]]
    | y :: ys => (x :: y) :: ys

def List.md (A : Type) [DecidableEq A] [Min A] (seq : List A) : List (List A) :=
  match seq.min? with
  | none => []
  | some mini => seq.splitOn mini

def IterList (A : Type) : Nat → Type
  | 0 => A
  | n + 1 => IterList (List A) n

inductive NFClosed (A : Type) [DecidableEq A] [Min A]
  (P : List (List A) → Prop) : List A → Prop where
| mk (xs : List A)
  (h₁ : P (List.md A xs))
  (h₂ : ∀ ys ∈ List.md A xs, NFClosed A P ys) :
  NFClosed A P xs

def NF (A : Type)
  [LT A] [strict_linear_order A]
  [DecidableEq A] [DecidableLT A]
  (n : Nat) (xs : List A) : Prop :=
  match n with
  | 0 => xs.Pairwise (fun x y => y < x ∨ y = x)
  | m + 1 =>
    NFClosed A (fun ys => NF (List A) m ys) xs

def NFAt (A : Type)
  [LT A] [strict_linear_order A]
  [DecidableEq A] [DecidableLT A]
  (depth : Nat) :
  (k : Nat) → List (IterList A k) → Prop
  | 0, xs => NF A depth xs
  | k + 1, xs => NFAt (List A) depth k xs

def NF_k (A : Type)
  [LT A] [strict_linear_order A]
  [DecidableEq A] [DecidableLT A]
  (n k : Nat) (_hk : 1 ≤ k ∧ k ≤ n)
  (xs : List (IterList A (k - 1))) : Prop :=
  NFAt A (n - k + 1) (k - 1) xs

def generalizedBeklemishevConjecture : Prop :=
  ∀ (A : Type)
    [LT A] [strict_linear_order A]
    [DecidableEq A] [DecidableLT A],
    WellFounded (fun x y : A => x < y) →
    ∀ n : Nat,
      WellFounded
        (fun x y : {xs : List A // NF A n xs} =>
          x.val < y.val)
