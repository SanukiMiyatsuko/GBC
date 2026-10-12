import Mbekworm.Sequence.NormalForm
import Mbekworm.Buchholz.Rank1

/-!
# The ordinal semantics of `expand M` in rank-one Buchholz terms

A sequence of naturals is read as a *worm*; worms of level `m` over countable
ordinal letters (rank-one terms) are valued by `o m`.  For a list of naturals,
`o M` splits at the letter `0`, decrements the pieces and evaluates the
resulting worm of level `M - 1` over ordinal letters.  Worms whose least letter
`μ` is positive are evaluated through the hyperation `E m μ`, whose building
blocks are the Veblen-type functions `phi k a ξ = ψ₀(Ω^(Ω·k + a)·(1 + ξ))`,
computed with absorption so that the result is a normal form.
-/

open T

namespace Sem

/-- `1`. -/
def one : T := P 0 Z Z
/-- `Ω`. -/
def Om : T := P 1 Z Z
/-- Ordinal addition of summand chains: summands of `x` below the head of `y` are absorbed. -/
def oadd : T → T → T
  | Z, y => y
  | P i a b, y => if P i a Z < T.head y then y else P i a (oadd b y)

/-- `-1 + x`. -/
def minus1 : T → T
  | P 0 Z b => b
  | x => x

/-- `1 + x`. -/
def onePlus : T → T
  | Z => one
  | P 0 Z b => P 0 Z (P 0 Z b)
  | x => x

/-- The leading summands of index `≥ 1`. -/
def uncPart : T → T
  | Z => Z
  | P 0 _ _ => Z
  | P (i + 1) a b => P (i + 1) a (uncPart b)

/-- What is left after the leading summands of index `≥ 1`. -/
def cntPart : T → T
  | Z => Z
  | P 0 a b => P 0 a b
  | P (_ + 1) _ b => cntPart b

/-- The exponent `λ` with `ψ₀(c) = ω^λ`. -/
def logA (c : T) : T :=
  if uncPart c = Z then c else oadd (P 0 (uncPart c) Z) (cntPart c)

/-- `ω^y`, in normal form, for countable `y`. -/
def omegaPow : T → T
  | Z => one
  | P i c b =>
    if uncPart c = Z then P 0 (P i c b) Z
    else if cntPart c = Z then P 0 (T.add (uncPart c) b) Z
    else P 0 (T.add (uncPart c) (P i c b)) Z

/-- `Ω · x` for countable `x`. -/
def omegaTimes : T → T
  | Z => Z
  | P _ c b => P 1 (logA c) (omegaTimes b)

/-- `n` copies of the summand `P 1 x Z`. -/
def copies (x : T) : Nat → T
  | 0 => Z
  | n + 1 => P 1 x (copies x n)

/-- `Ω · (Ω·k + a)`. -/
def OG (k : Nat) (a : T) : T := T.add (copies Om k) (omegaTimes a)

/-- `-Ω + x`. -/
def dropOm : T → T
  | P 1 Z b => b
  | x => x

/-- `Ω^(Ω·k + a) · x` for countable `x`. -/
def OPowTimes (k : Nat) (a : T) : T → T
  | Z => Z
  | P _ c b => P 1 (dropOm (T.add (OG k a) (logA c))) (OPowTimes k a b)

/-- `x ≤ y`, as a boolean. -/
def leB (x y : T) : Bool := decide (x ≤ y)

/-- The longest prefix of summands satisfying `p`. -/
def takeW (p : Nat → T → Bool) : T → T
  | Z => Z
  | P i a b => if p i a then P i a (takeW p b) else Z

/-- Summands of the head argument of `a` lying at level `≥ k + 1`. -/
def alphaHead (k : Nat) : T → T
  | Z => Z
  | P _ d _ => takeW (fun i c => decide (2 ≤ i) || (decide (1 ≤ i) && leB (copies Om (k + 1)) c)) d

/-- Summands whose exponent reaches `thr`. -/
def bigW (thr : T) (i : Nat) (c : T) : Bool :=
  decide (2 ≤ i) || (decide (1 ≤ i) && leB thr (oadd Om c))

/-- `φ_k(a, ξ) = ψ₀(Ω^(Ω·k + a) · (1 + ξ))`, with absorption of fixed points. -/
def phi (k : Nat) (a ξ : T) : T :=
  let B := alphaHead k a
  let pure : Bool := decide (B ≠ Z) && decide (a = P 0 B Z)
  let dflt := P 0 (T.add B (OPowTimes k a (if pure then ξ else onePlus ξ))) Z
  match ξ with
  | Z => dflt
  | P i d b =>
    let D := takeW (bigW (oadd (OG k a) Om)) d
    if B < D then P 0 (T.add D (OPowTimes k a (if d = D then b else P i d b))) Z
    else dflt

/-- Apply `f (log c)` for the summands `P _ c _` of `μ`, the last summand innermost. -/
def foldE (f : T → T → T) : T → T → T
  | Z, x => x
  | P _ c b, x => f (logA c) (foldE f b x)

/-- The hyperation `E m μ`. -/
def E : Nat → T → T → T
  | 0, _, x => x
  | 1, μ, x => foldE (fun α y =>
      if α = Z then minus1 (omegaPow y) else if y = Z then Z else phi 0 α (minus1 y)) μ x
  | m + 2, μ, x => foldE (fun α y =>
      if α = Z then minus1 (E (m + 1) y one) else if y = Z then Z
      else phi (m + 1) (minus1 α) (minus1 y)) μ x

/-- `-μ + x`. -/
def leftSub : T → T → T
  | Z, x => x
  | P _ _ _, Z => Z
  | P i a b, P j c d => if i = j ∧ a = c then leftSub b d else P j c d

/-- The least letter (or `Z`). -/
def tmin (w : List T) : T := w.min?.getD Z

/-- Cantor normal form `ω^b₀ + ω^b₁ + ⋯`. -/
def cantorT : List T → T
  | [] => Z
  | b :: bs => oadd (omegaPow b) (cantorT bs)

/-- The value of a worm of level `m` over countable ordinal letters. -/
def o : Nat → List T → T
  | _, [] => Z
  | 0, b :: bs => cantorT (b :: bs)
  | m + 1, x :: xs =>
    let w := x :: xs
    let μ := tmin w
    let w' := w.map (leftSub μ)
    E (m + 1) μ
      (if hZ : Z ∈ w' then
        minus1 (o m ((GenBek.sepPieces Z w').attach.map
          (fun p => o (m + 1) (p.val.map minus1))))
      else Z)
termination_by m w => (m, w.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
    | (apply Prod.Lex.right
       have h := GenBek.length_lt_of_mem_sepPieces Z w' hZ p.val p.property
       simp only [List.length_map] at h ⊢
       simpa [w', w] using h)

/-- The translation of a sequence of naturals. -/
def trM (M : Nat) (xs : List Nat) : T := o M (xs.map T.ofNat)

end Sem
