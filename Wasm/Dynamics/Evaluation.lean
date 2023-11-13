import Wasm.Util
import Wasm.Syntax.Value

namespace Wasm.Dynamics.Evaluation

namespace Numeric

open Syntax.Value

namespace Unsigned

open Syntax.Value.Unsigned

def sat (i : Int) : Unsigned n :=
  if i > (@MAX_VALUE n).toNat then MAX_VALUE
  else if i < 0 then 0
  else ofInt i

theorem mod_size : x % MAX n < Nat.pow 2 n := by
  rw [MAX]
  exact Nat.mod_lt x zero_lt_two_pow

def add (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val + i₂.val) % MAX n, mod_size⟩
instance : Add (Unsigned n) := ⟨add⟩

def sub (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val - i₂.val + MAX n) % MAX n, mod_size⟩
instance : Sub (Unsigned n) := ⟨sub⟩

def neg (i : Unsigned n) : Unsigned n :=
  ⟨(MAX n - i.val) % MAX n, mod_size⟩
instance : Neg (Unsigned n) := ⟨neg⟩

def mul (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val * i₂.val) % MAX n, mod_size⟩
instance : Mul (Unsigned n) := ⟨mul⟩

def divOpt (i j : Unsigned n) : Option (Unsigned n) :=
  match Unsigned.compare (ofNat 0) j with
  | .eq => .none
  | _   => .some <| ofNat (i.toNat / j.toNat)
instance : HDiv (Unsigned n) (Unsigned n) (Option (Unsigned n)) := ⟨divOpt⟩

def remOpt (i j : Unsigned n) : Option (Unsigned n) :=
  match Unsigned.compare (ofNat 0) j with
  | .eq => .none
  | _   => .some <| ofNat (i.toNat - j.toNat * (i.toNat / j.toNat))
instance : HMod (Unsigned n) (Unsigned n) (Option (Unsigned n)) := ⟨remOpt⟩

def and (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val &&& i₂.val) % MAX n, mod_size⟩
instance : HAnd (Unsigned n) (Unsigned n) (Unsigned n) := ⟨and⟩

def or (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val ||| i₂.val) % MAX n, mod_size⟩
instance : HOr (Unsigned n) (Unsigned n) (Unsigned n) := ⟨or⟩

def xor (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val ^^^ i₂.val) % MAX n, mod_size⟩
instance : HXor (Unsigned n) (Unsigned n) (Unsigned n) := ⟨xor⟩

def not (i : Unsigned n) : Unsigned n :=
  ⟨(i.val ^^^ (MAX_VALUE : Unsigned n).val) % MAX n, mod_size⟩
instance : Complement (Unsigned n) := ⟨not⟩

def andnot (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val &&& (~~~i₂).val) % MAX n, mod_size⟩
  -- ⟨(Unsigned.and i₁ (Unsigned.not i₂)) % MAX n, mod_size⟩

def shl (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val <<< i₂.val) % MAX n, mod_size⟩
instance : HShiftLeft (Unsigned n) (Unsigned n) (Unsigned n) := ⟨shl⟩

def shr (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val >>> i₂.val) % MAX n, mod_size⟩
instance : HShiftRight (Unsigned n) (Unsigned n) (Unsigned n) := ⟨shr⟩

-- stolen from my WASM interpreter I wrote in C
def rotl (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val <<< i₂.val) ||| (i₁.val >>> (n - i₂.val))) % MAX n, mod_size⟩

def rotr (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val >>> i₂.val) ||| (i₁.val <<< (n - i₂.val))) % MAX n, mod_size⟩

-- not doing the efficient datalab solution, also a little scuffed anyway
def clz (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (n - (clz_helper i n.val))
where clz_helper (i : Unsigned n) (c : Nat) : Nat :=
  if h : c = 0
  then c
  else if (rotl i (ofNat (n - c + 1))) &&& 1 = 1
  then c
  else clz_helper i (c - 1)

def ctz (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (n - (ctz_helper i n.val))
where ctz_helper (i : Unsigned n) (c : Nat) : Nat :=
  if h : c = 0
  then c
  else if (i >>> (ofNat (n - c) : Unsigned n)) &&& 1 = 1
  then c
  else ctz_helper i (c - 1)

-- people really made a log n algorithm for an O(32) problem
def popcnt (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (popcnt_helper n i 0)
where popcnt_helper (f : Nat) (i : Unsigned n) (c : Nat) : Nat :=
  if h : f = 0
  then c
  else if (i >>> (ofNat (n - f) : Unsigned n)) &&& 1 = 1
  then popcnt_helper (f - 1) i (c + 1)
  else popcnt_helper (f - 1) i c


-- COMPARISON FUNCTIONS

def eqz (i : Unsigned n) : Unsigned n :=
  if i = .ofNat 0 then .ofNat 1 else .ofNat 0
def eq (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ = i₂ then .ofNat 1 else .ofNat 0
def ne (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≠ i₂ then .ofNat 1 else .ofNat 0
def lt (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ < i₂ then .ofNat 1 else .ofNat 0
def gt (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ > i₂ then .ofNat 1 else .ofNat 0
def le (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≤ i₂ then .ofNat 1 else .ofNat 0
def ge (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≥ i₂ then .ofNat 1 else .ofNat 0

-- CONVERSION

def extend (i : Unsigned n) : Unsigned m := .ofNat i.toNat
def wrap   (i : Unsigned n) : Unsigned m := .ofNat (i.val % MAX n)

-- MISC FUNCTIONS

def bitselect (i₁ i₂ i₃ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val &&& i₃.val) ||| (i₂.val &&& (~~~i₃).val)) % MAX n, mod_size⟩

def min (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ < i₂ then i₁ else i₂
def max (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ > i₂ then i₁ else i₂

def addsat (i₁ i₂ : Unsigned n) : Unsigned n := sat (i₁.val + i₂.val)
def subsat (i₁ i₂ : Unsigned n) : Unsigned n := sat (i₁.val - i₂.val)
def avgr (i₁ i₂ : Unsigned n)   : Unsigned n :=
  Unsigned.ofNat ((i₁.val + i₂.val + 1) / 2)

end Unsigned

namespace Signed

open Syntax.Value.Signed

def sat (i : Int) : Signed n :=
  if i < (@MIN_VALUE n).toInt then MIN_VALUE
  else if i > (@MAX_VALUE n).toInt then MAX_VALUE
  else ofInt i

def add : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.add
instance : Add (Signed n) := ⟨add⟩

def sub : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.sub
instance : Sub (Signed n) := ⟨sub⟩

def neg : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.neg
instance : Neg (Signed n) := ⟨neg⟩

def mul : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.mul
instance : Mul (Signed n) := ⟨mul⟩

def divOpt (i j : Signed n) : Option (Signed n) :=
  match Signed.compare (.ofUnsignedN 0) j with
  | .eq => .none
  | _   => validate (i.toInt / j.toInt)
where validate (res : ℤ) : Option (Signed n) :=
  if res = -(MIN_VALUE : Signed n).toInt
  then .none
  else .some (.ofInt res)
instance : HDiv (Signed n) (Signed n) (Option (Signed n)) := ⟨divOpt⟩

def remOpt (i j : Signed n) : Option (Signed n) :=
  match Signed.compare (.ofUnsignedN 0) j with
  | .eq => .none
  | _   => .some <| (i.toInt - j.toInt * (i.toInt / j.toInt)) |> .ofInt
instance : HMod (Signed n) (Signed n) (Option (Signed n)) := ⟨remOpt⟩

def rem (i j : Signed n) (h : j ≠ 0) : Signed n :=
  (i.toInt - j.toInt * (i.toInt / j.toInt)) |> .ofInt


def and : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.and
instance : HAnd (Signed n) (Signed n) (Signed n) := ⟨and⟩

def or : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.or
instance : HOr (Signed n) (Signed n) (Signed n) := ⟨or⟩

def xor : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.xor
instance : HXor (Signed n) (Signed n) (Signed n) := ⟨xor⟩

def not : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.not
instance : Complement (Signed n) := ⟨not⟩

def andnot : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.andnot

def shl : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.shl
instance : HShiftLeft (Signed n) (Signed n) (Signed n) := ⟨shl⟩

def shr (i₁ i₂ : Signed n) : Signed n :=
  ⟨((i₁.val >>> i₂.val) ||| (i₁.val &&& 1 <<< 31)) % Unsigned.MAX n, Unsigned.mod_size⟩
instance : HShiftRight (Signed n) (Signed n) (Signed n) := ⟨shr⟩

def rotl : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.rotl

def rotr : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.rotr

def clz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.clz

def ctz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.ctz

def popcnt : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.popcnt


-- COMPARISON FUNCTIONS

def eqz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.eqz
def eq : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.eq
def neq : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.ne
def lt (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt < i₂.toInt then .ofNat 1 else .ofNat 0
def gt (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt > i₂.toInt then .ofNat 1 else .ofNat 0
def le (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt ≤ i₂.toInt then .ofNat 1 else .ofNat 0
def ge (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt ≥ i₂.toInt then .ofNat 1 else .ofNat 0

-- CONVERSION FUNCTIONS

def extend (i : Signed n) : Signed m := .ofInt i.toInt
def wrap : Signed n → Signed m := cast (by unfold Signed; rfl) Unsigned.wrap

-- MISC FUNCTIONS

def bitselect : Signed n → Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.bitselect

def abs (i : Signed n) : Signed n :=
  if i ≥ 0 then i else -i

def min (i₁ i₂ : Signed n) : Signed n :=
  if lt i₁ i₂ = 1 then i₁ else i₂
def max (i₁ i₂ : Signed n) : Signed n :=
  if gt i₁ i₂ = 1 then i₁ else i₂

def addsat (i₁ i₂ : Signed n) : Signed n := sat (i₁.toInt + i₂.toInt)
def subsat (i₁ i₂ : Signed n) : Signed n := sat (i₁.toInt - i₂.toInt)

end Signed

end Numeric
