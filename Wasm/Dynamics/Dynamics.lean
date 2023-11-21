import Wasm.Util
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance
import Wasm.Dynamics.Stack
import Wasm.Dynamics.Evaluation
import Wasm.Dynamics.Context
import Wasm.Dynamics.Instr
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Instr
import Numbers
open Numbers

namespace Wasm.Dynamics

@[inline] def Step := Dynamics.Context.Config → Dynamics.Context.Config → Prop

open Wasm.Syntax.Instr
open Wasm.Syntax.Value
open Wasm.Dynamics.Evaluation
open Wasm.Dynamics.Evaluation.Numeric

def int {nn : Numeric.Size}
        (instr : Syntax.Instr.Numeric.Integer nn)
        : Dynamics.Instr.Dynamic :=
  .real (.numeric ((.integer instr) : (Syntax.Instr.Numeric nn)))

def const {nn : Numeric.Size} (v : Unsigned nn.toBits) :=
  int (.const v)

namespace Step.Numeric.Integer

def iunop {nn : Numeric.Size}
          (op : Syntax.Instr.Numeric.Integer.Unop)
          : Dynamics.Instr.Dynamic :=
  @int nn (.unop op)

inductive Unop : Step
| clz     : {nn : Numeric.Size}
          → {c : Unsigned (Numeric.Size.toBits nn)}
          → Unop (s, (f, iunop .clz :: const c :: is))
                 (s, (f, const (Unsigned.clz c) :: is))
| ctz     : {nn : Numeric.Size}
          → {c : Unsigned (Numeric.Size.toBits nn)}
          → Unop (s, (f, iunop .ctz :: const c :: is))
                 (s, (f, const (Unsigned.clz c) :: is))
| popcnt  : {nn : Numeric.Size}
          → {c : Unsigned (Numeric.Size.toBits nn)}
          → Unop (s, (f, iunop .popcnt :: const c :: is))
                 (s, (f, const (Unsigned.clz c) :: is))

def ibinop {nn : Numeric.Size}
           (op : Syntax.Instr.Numeric.Integer.Binop)
           : Dynamics.Instr.Dynamic :=
  @int nn (.binop op)


inductive Binop : Step
| add     : Binop (s, (f, ibinop .add :: const c₂ :: const c₁ :: is))
                  (s, (f, const (c₁ + c₂) :: is))
| sub     : Binop (s, (f, ibinop .sub :: const c₂ :: const c₁ :: is))
                  (s, (f, const (c₁ - c₂) :: is))
| mul     : Binop (s, (f, ibinop .mul :: const c₂ :: const c₁ :: is))
                  (s, (f, const (c₁ * c₂) :: is))
| div_u_t : Unsigned.divOpt c₁ c₂ = .none
          → Binop (s, (f, ibinop (.div .u) :: const c₂ :: const c₁ :: is))
                  (s, (f, .admin .trap :: is))
| div_u   : Unsigned.divOpt c₁ c₂ = .some c
          → Binop (s, (f, ibinop (.div .u) :: const c₂ :: const c₁ :: is))
                  (s, (f, const c :: is))
| div_s_t : Signed.divOpt c₁ c₂ = .none
          → Binop (s, (f, ibinop (.div .s) :: const c₂ :: const c₁ :: is))
                  (s, (f, .admin .trap :: is))
| div_s   : Signed.divOpt c₁ c₂ = .some c
          → Binop (s, (f, ibinop (.div .s) :: const c₂ :: const c₁ :: is))
                  (s, (f, const c :: is))
| mod_u_t : Unsigned.remOpt c₁ c₂ = .none
          → Binop (s, (f, ibinop (.mod .u) :: const c₂ :: const c₁ :: is))
                  (s, (f, .admin .trap :: is))
| mod_u   : Unsigned.remOpt c₁ c₂ = .some c
          → Binop (s, (f, ibinop (.mod .u) :: const c₂ :: const c₁ :: is))
                  (s, (f, const c :: is))
| mod_s_t : Signed.remOpt c₁ c₂ = .none
          → Binop (s, (f, ibinop (.mod .s) :: const c₂ :: const c₁ :: is))
                  (s, (f, .admin .trap :: is))
| mod_s   : Signed.remOpt c₁ c₂ = .some c
          → Binop (s, (f, ibinop (.mod .s) :: const c₂ :: const c₁ :: is))
                  (s, (f, const c :: is))
| and     : Binop (s, (f, ibinop .and :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.and c₁ c₂) :: is))
| or      : Binop (s, (f, ibinop .or :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.or c₁ c₂) :: is))
| xor     : Binop (s, (f, ibinop .xor :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.xor c₁ c₂) :: is))
| shl     : Binop (s, (f, ibinop .shl :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.shl c₁ c₂) :: is))
| shr_u   : Binop (s, (f, ibinop (.shr .u) :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.shr c₁ c₂) :: is))
| shr_s   : Binop (s, (f, ibinop (.shr .s) :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Signed.shr c₁ c₂) :: is))
| rotl    : Binop (s, (f, ibinop .rotl :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.rotl c₁ c₂) :: is))
| rotr    : Binop (s, (f, ibinop .rotr :: const c₂ :: const c₁ :: is))
                  (s, (f, const (Unsigned.rotr c₁ c₂) :: is))

inductive Test : Step
| eqz : Test (s, (f, int (.test .eqz) :: const c₁ :: is))
             (s, (f, const (Unsigned.eqz c₁) :: is))

def irelop {nn : Numeric.Size}
           (op : Syntax.Instr.Numeric.Integer.Relation)
           : Dynamics.Instr.Dynamic :=
  @int nn (.relation op)

inductive Relation : Step
| eq    : Relation (s, (f, irelop .eq :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.eq c₁ c₂) :: is))
| ne    : Relation (s, (f, irelop .ne :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.ne c₁ c₂) :: is))
| lt_u  : Relation (s, (f, irelop (.lt .u) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.lt c₁ c₂) :: is))
| gt_u  : Relation (s, (f, irelop (.gt .u) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.gt c₁ c₂) :: is))
| le_u  : Relation (s, (f, irelop (.le .u) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.le c₁ c₂) :: is))
| ge_u  : Relation (s, (f, irelop (.ge .u) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Unsigned.ge c₁ c₂) :: is))
| lt_s  : Relation (s, (f, irelop (.lt .s) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Signed.lt c₁ c₂) :: is))
| gt_s  : Relation (s, (f, irelop (.gt .s) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Signed.gt c₁ c₂) :: is))
| le_s  : Relation (s, (f, irelop (.le .s) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Signed.le c₁ c₂) :: is))
| ge_s  : Relation (s, (f, irelop (.ge .s) :: const c₂ :: const c₁ :: is))
                   (s, (f, const (Signed.ge c₁ c₂) :: is))

end Integer

inductive Integer : Step
| unop        : Integer.Unop config config' → Integer config config'
| binop       : Integer.Binop config config' → Integer config config'
| test        : Integer.Test config config' → Integer config config'
| relation    : Integer.Relation config config' → Integer config config'
| extend8_s   : {nn mm : Numeric.Size}
              → {c₁ : Signed (Numeric.Size.toBits mm)}
              → {c₂ : Signed (Numeric.Size.toBits nn)}
              → {_ : (Signed.extend ((Signed.extend c₁) : Signed8)) = c₂}
              → Integer (s, (f, int .extend8_s :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
| extend16_s  : {nn mm : Numeric.Size}
              → {c₁ : Signed (Numeric.Size.toBits mm)}
              → {c₂ : Signed (Numeric.Size.toBits nn)}
              → {_ : (Signed.extend ((Signed.extend c₁) : Signed16)) = c₂}
              → Integer (s, (f, int .extend16_s :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
| extend32_s  : {nn mm : Numeric.Size}
              → {c₁ : Signed (Numeric.Size.toBits mm)}
              → {c₂ : Signed (Numeric.Size.toBits nn)}
              → {_ : (Signed.extend ((Signed.extend c₁) : Signed32)) = c₂}
              → Integer (s, (f, int .extend32_s :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
| wrap_i64    : {mm : Numeric.Size}
              → {c₁ : Signed (Numeric.Size.toBits mm)}
              → {c₂ : Signed (Numeric.Size.toBits .quad)}
              → {_ : Signed.wrap c₁ = c₂}
              → Integer (s, (f, int .wrap_i64 :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
| extend_u32  : {c₁ : Unsigned (Numeric.Size.toBits .double)}
              → {c₂ : Unsigned (Numeric.Size.toBits .quad)}
              → {_ : (Unsigned.extend c₁) = c₂}
              → Integer (s, (f, int (.extend_i32 .u) :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
| extend_s32  : {c₁ : Signed (Numeric.Size.toBits .double)}
              → {c₂ : Signed (Numeric.Size.toBits .quad)}
              → {_ : (Signed.extend c₁) = c₂}
              → Integer (s, (f, int (.extend_i32 .s) :: const c₁ :: is))
                        (s, (f, const c₂ :: is))
-- todo: add trunc/reinterpret

end Numeric

inductive Numeric : Step
| integer : Numeric.Integer config config' → Numeric config config'
| float   : False → Numeric config config' -- todo



def ref (instr : Syntax.Instr.Reference)
        : Dynamics.Instr.Dynamic :=
  .real (.reference instr)

inductive Reference : Step
| null      : IsValue (ref (.null t)) (.ref (.null _))
            → Reference (s, (f, ref .is_null :: ref (.null t) :: is))
                        (s, (f, const (.ofNat 1) :: is))
| non_null  : IsValue val _
            → Reference (s, (f, ref .is_null :: val :: is))
                        (s, (f, const (.ofNat 0) :: is))
| func      : Reference (s, (f, ref (.func (Vec.index f.module.funcaddrs x)) :: is))
                        (s, (f, .admin (.ref (f.module.funcaddrs.get x)) :: is))

def locl (instr : Syntax.Instr.Local)
         : Dynamics.Instr.Dynamic :=
  .real (.locl instr)

inductive Local : Step
| get : Local (s, (f, locl (.get (Vec.index f.locals x)) :: is))
              (s, (f, Value.instr (f.locals.get x) :: is))
| set : {_ : IsValue val v}
      → Local (s, (f, locl (.set (Vec.index f.locals x)) :: val :: is))
              (s, ({f with locals := f.locals.set x v}, is))
| tee : {_ : IsValue val₁ v₁}
      → Local (s, (f, locl (.tee (Vec.index f.locals x)) :: val :: is))
              (s, (f, locl (.set (Vec.index f.locals x)) :: val :: val :: is))

def globl (instr : Syntax.Instr.Global)
          : Dynamics.Instr.Dynamic :=
  .real (.globl instr)

inductive Global : Step
| get : {a : Fin (Vec.length s.globals)}
      → {_ : Vec.index s.globals a = f.module.globaladdrs.get x}
      → Global (s, (f, globl (.get (Vec.index f.module.globaladdrs x)) :: is))
               (s, (f, Value.instr (s.globals.get a).value :: is))
| set : {a : Fin (Vec.length s.globals)}
      → {_ : Vec.index s.globals a = f.module.globaladdrs.get x}
      → {_ : IsValue val v}
      → Global (s, (f, globl (.set (Vec.index f.module.globaladdrs x)) :: val :: is))
               ({s with globals := s.globals.set a {s.globals.get a with value := v}}, (f, is))

def table (instr : Syntax.Instr.Table)
          : Dynamics.Instr.Dynamic :=
  .real (.table instr)

inductive Table : Step
| get     : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {h : i.toNat < tab.elem.length}
          → Table (s, (f, table (.get (Vec.index f.module.tableaddrs x)) :: @const .double i :: is))
                  (s, (f, Value.instr (tab.elem.get ⟨i.toNat, h⟩ |> .ref) :: is))
| get_t   : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {_ : i.toNat ≥ tab.elem.length}
          → Table (s, (f, table (.get (Vec.index f.module.tableaddrs x)) :: @const .double i :: is))
                  (s, (f, .admin .trap :: is))
| set     : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {_ : IsValue val (.ref v)}
          → {h : i.toNat < tab.elem.length}
          → Table (s, (f, table (.set (Vec.index f.module.tableaddrs x)) :: val :: @const .double i :: is))
                  ({s with tables := s.tables.set a {tab with elem := tab.elem.set ⟨i.toNat, h⟩ v}}, (f, is))
| set_t   : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {_ : IsValue val (.ref v)}
          → {_ : i.toNat ≥ tab.elem.length}
          → Table (s, (f, table (.set (Vec.index f.module.tableaddrs x)) :: val :: @const .double i :: is))
                  (s, (f, .admin .trap :: is))
| size    : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → Table (s, (f, table (.size (Vec.index f.module.tableaddrs x)) :: is))
                  (s, (f, @const .double ⟨tab.elem.length, tab.elem.maxLen⟩ :: is))
| grow    : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {h : sz  = tab.elem.length}
          → {_ : IsValue val (.ref v)}
          → {_ : False} -- todo implement growtable {_ : .some tab' = growtable (tab, n, v)}
          → {_ : s' = {s with tables := s.tables.set a tab'}}
          → Table (s, (f, table (.grow (Vec.index f.module.tableaddrs x)) :: @const .double n :: val :: is))
                  (s', (f, @const .double ⟨sz, by rw [h]; exact tab.elem.maxLen⟩ :: is))
| grow_e  : {a : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables a = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get a}
          → {_ : sz  = tab.elem.length}
          → {_ : IsValue val (.ref v)}
          → {_ : False} -- todo implement growtable {_ : .none = growtable (tab, n, v)}
          → Table (s, (f, table (.grow (Vec.index f.module.tableaddrs x)) :: @const .double n :: val :: is))
                  (s, (f, @const .double (Signed.ofInt (-1)) :: is))
| fill    : {ta : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : IsValue val (.ref v)}
          → {_ : i.toNat + n.toNat + 1 ≤ tab.elem.length}
          → Table (s, (f, table (.fill (Vec.index f.module.tableaddrs x))
                       :: @const .double (n + 1)
                       :: val
                       :: @const .double i
                       :: is))
                  (s, (f, table (.fill (Vec.index f.module.tableaddrs x))
                       :: const n
                       :: val
                       :: const (i + 1)
                       :: table (.set (Vec.index f.module.tableaddrs x))
                       :: val
                       :: const (i)
                       :: is))
| fill_z  : {ta : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : IsValue val (.ref v)}
          → {_ : i.toNat ≤ tab.elem.length}
          → Table (s, (f, table (.fill (Vec.index f.module.tableaddrs x))
                       :: @const .double 0
                       :: val
                       :: @const .double i
                       :: is))
                  (s, (f, is))
| fill_t  : {ta : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : IsValue val (.ref v)}
          → {_ : i.toNat + n.toNat > tab.elem.length}
          → Table (s, (f, table (.fill (Vec.index f.module.tableaddrs x))
                       :: @const .double n
                       :: val
                       :: @const .double i
                       :: is))
                  (s, (f, .admin .trap :: is))
| copy_le : {ta_x ta_y : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta_x = f.module.tableaddrs.get x}
          → {_ : tab_x = s.tables.get ta_x}
          → {_ : Vec.index s.tables ta_y = f.module.tableaddrs.get y}
          → {_ : tab_y = s.tables.get ta_y}
          → {_ : (src.toNat + n.toNat ≤ tab_y.elem.length)}
          → {_ : d.toNat + n.toNat + 1 ≤ tab_x.elem.length}
          → {_ : d ≤ src}
          → Table (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: @const .double (n + 1)
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: const n
                       :: const (src + 1)
                       :: const (d + 1)
                       :: table (.set (Vec.index f.module.tableaddrs x))
                       :: table (.get (Vec.index f.module.tableaddrs y))
                       :: const src
                       :: const d
                       :: is))
| copy_gt : {ta_x ta_y : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta_x = f.module.tableaddrs.get x}
          → {_ : tab_x = s.tables.get ta_x}
          → {_ : Vec.index s.tables ta_y = f.module.tableaddrs.get y}
          → {_ : tab_y = s.tables.get ta_y}
          → {_ : (src.toNat + n.toNat + 1 ≤ tab_y.elem.length)}
          → {_ : d.toNat + n.toNat + 1 ≤ tab_x.elem.length}
          → {_ : d > src}
          → Table (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: @const .double (n + 1)
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: const n
                       :: const src
                       :: const d
                       :: table (.set (Vec.index f.module.tableaddrs x))
                       :: table (.get (Vec.index f.module.tableaddrs y))
                       :: const (src + n)
                       :: const (d + n)
                       :: is))
| copy_z  : {ta_x ta_y : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta_x = f.module.tableaddrs.get x}
          → {_ : tab_x = s.tables.get ta_x}
          → {_ : Vec.index s.tables ta_y = f.module.tableaddrs.get y}
          → {_ : tab_y = s.tables.get ta_y}
          → {_ : src.toNat ≤ tab_y.elem.length}
          → {_ : d.toNat ≤ tab_x.elem.length}
          → Table (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: @const .double 0
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, is))
| copy_t  : {ta_x ta_y : Fin (Vec.length s.tables)}
          → {_ : Vec.index s.tables ta_x = f.module.tableaddrs.get x}
          → {_ : tab_x = s.tables.get ta_x}
          → {_ : Vec.index s.tables ta_y = f.module.tableaddrs.get y}
          → {_ : tab_y = s.tables.get ta_y}
          → {_ : (src.toNat + n.toNat > tab_y.elem.length)
               ∨ (d.toNat + n.toNat > tab_x.elem.length)}
          → Table (s, (f, table (.copy (Vec.index f.module.tableaddrs x) (Vec.index f.module.tableaddrs y))
                       :: @const .double n
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, .admin .trap :: is))
| init    : {ta : Fin (Vec.length s.tables)}
          → {ea : Fin (Vec.length s.elems)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : Vec.index s.elems ea = f.module.elemaddrs.get y}
          → {_ : elem = s.elems.get ea}
          → {h₁ : src.toNat + (n.toNat + 1) ≤ elem.elem.length}
          → {h₂ : d.toNat + (n.toNat + 1) ≤ elem.elem.length}
          → {_ : IsValue val (.ref v)}
          → {_h : v = elem.elem.get ⟨src.toNat, by rw [Nat.add_succ, Nat.succ_le] at h₁; exact lt_left_add h₁⟩}
          → {_ : d.toNat + 1 < Unsigned.MAX ⟨32, by simp⟩} -- prove using h₂, like in h
          → {_ : src.toNat + 1 < Unsigned.MAX ⟨32, by simp⟩} -- prove using h₁, like in h
          → Table (s, (f, table (.init (Vec.index f.module.tableaddrs x) (Vec.index f.module.elemaddrs y))
                       :: @const .double (n + 1)
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, table (.init (Vec.index f.module.tableaddrs x) (Vec.index f.module.elemaddrs y))
                       :: const n
                       :: const (src + 1)
                       :: const (d + 1)
                       :: table (.set (Vec.index f.module.tableaddrs x))
                       :: val
                       :: const d
                       :: is))
| init_z  : {ta : Fin (Vec.length s.tables)}
          → {ea : Fin (Vec.length s.elems)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : Vec.index s.elems ea = f.module.elemaddrs.get y}
          → {_ : elem = s.elems.get ea}
          → {_ : src.toNat ≤ elem.elem.length}
          → {_ : d.toNat ≤ elem.elem.length}
          → Table (s, (f, table (.init (Vec.index f.module.tableaddrs x) (Vec.index f.module.elemaddrs y))
                       :: @const .double 0
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, is))
| init_t  : {ta : Fin (Vec.length s.tables)}
          → {ea : Fin (Vec.length s.elems)}
          → {_ : Vec.index s.tables ta = f.module.tableaddrs.get x}
          → {_ : tab = s.tables.get ta}
          → {_ : Vec.index s.elems ea = f.module.elemaddrs.get y}
          → {_ : elem = s.elems.get ea}
          → {_ : src.toNat + n.toNat > elem.elem.length
               ∨ d.toNat + n.toNat > elem.elem.length}
          → Table (s, (f, table (.init (Vec.index f.module.tableaddrs x) (Vec.index f.module.elemaddrs y))
                       :: @const .double n
                       :: @const .double src
                       :: @const .double d
                       :: is))
                  (s, (f, .admin .trap :: is))

def mem (instr : Syntax.Instr.Memory)
        : Dynamics.Instr.Dynamic :=
  .real (.memory instr)

def mem_int (instr : Syntax.Instr.Memory.Integer nn)
            : Dynamics.Instr.Dynamic :=
  mem (.integer instr)

namespace Memory

/- todo: rewriting read/write memory

inductive Integer.Load (instr : Numeric.Sign → Memory.Arg → Memory.Integer nn)
               : (nBits : { i // 0 < i }) → Step
| unsigned  : {h : f.module.memaddrs.length > 0}
            → {a : Fin s.mems.length}
            → {n : Unsigned nBits}
            → {c : Unsigned nn.toBits}
            → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h⟩}
            → {_ : m = s.mems.get a}
            → {_ : ea = i.toNat + arg.offset.toNat}
            → {_ : ea + (nBits.val / 8) ≤ m.data.length}
            → {_ : b = (m.data.list.drop ea).take (nBits.val / 8)}
            → {_ : b = Unsigned.toBytes nBits n}
            → {_ : c = Unsigned.extend n}
            → Integer.Load instr nBits
                   (s, (f, @mem_int nn (instr .u arg) :: @const .double i :: is))
                   (s, (f, @const nn c :: is))
| signed    : {h : f.module.memaddrs.length > 0}
            → {a : Fin s.mems.length}
            → {n : Unsigned nBits}
            → {c : Signed nn.toBits}
            → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h⟩}
            → {_ : m = s.mems.get a}
            → {_ : ea = i.toNat + arg.offset.toNat}
            → {_ : ea + (nBits.val / 8) ≤ m.data.length}
            → {_ : b = (m.data.list.drop ea).take (nBits.val / 8)}
            → {_ : b = Unsigned.toBytes nBits n}
            → {_ : c = Signed.extend n}
            → Integer.Load instr nBits
                   (s, (f, @mem_int nn (instr .s arg) :: @const .double i :: is))
                   (s, (f, @const nn c :: is))
| trap      : {h : f.module.memaddrs.length > 0}
            → {a : Fin s.mems.length}
            → {n : Unsigned nBits}
            → {c : Unsigned nn.toBits}
            → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h⟩}
            → {_ : m = s.mems.get a}
            → {_ : ea = i.toNat + arg.offset.toNat}
            → {_ : ea + (nBits.val / 8) > m.data.length}
            → Integer.Load instr nBits
                   (s, (f, @mem_int nn (instr .u arg) :: @const .double i :: is))
                   (s, (f, .admin .trap :: is))

inductive Integer : Step
| load    : {nn : Numeric.Size}
          → {h₁ : f.module.memaddrs.length > 0}
          → {a : Fin s.mems.length}
          → {_ : nBytes = nn.toBytes}
          → {c : Unsigned nn.toBits}
          → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h₁⟩}
          → {_ : m = s.mems.get a}
          → {_ : ea = i.toNat + arg.offset.toNat}
          → {_ : ea + nBytes ≤ m.data.length}
          → {_ : b = ((m.data.list.drop ea).take nBytes)}
          → {_ : b = Unsigned.toBytes nn.toBits c}
          → Integer (s, (f, @mem_int nn (.load arg) :: @const .double i :: is))
                    (s, (f, @const nn c :: is))
| load_t  : {nn : Numeric.Size}
          → {h₁ : f.module.memaddrs.length > 0}
          → {a : Fin s.mems.length}
          → {_ : nBytes = nn.toBytes}
          → {c : Unsigned nn.toBits}
          → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h₁⟩}
          → {_ : m = s.mems.get a}
          → {_ : ea = i.toNat + arg.offset.toNat}
          → {_ : ea + nBytes > m.data.length}
          → Integer (s, (f, @mem_int nn (.load arg) :: @const .double i :: is))
                    (s, (f, .admin .trap :: is))
| load8   : Integer.Load .load8 ⟨8, by simp⟩ config config'
          → Integer config config'
| load16  : Integer.Load .load16 ⟨16, by simp⟩ config config'
          → Integer config config'
| load32  : Integer.Load .load32 ⟨32, by simp⟩ config config'
          → Integer config config'
| store   : {nn : Numeric.Size}
          → {h₁ : f.module.memaddrs.length > 0}
          → {a : Fin s.mems.length}
          → {c : Unsigned (Numeric.Size.toBits nn)}
          → {_ : nBytes = nn.toBytes}
          → {_ : Vec.index s.mems a = f.module.memaddrs.get ⟨0, h₁⟩}
          → {_ : m = s.mems.get a}
          → {_ : ea = i.toNat + arg.offset.toNat}
          → {_ : ea + nBytes ≤ m.data.length}
          → {_ : b = Unsigned.toBytes nn.toBits c}
          → {_ : m' = Instance.Memory.write m b ea}
        --   → {_ : s' = }
          → Integer (s, (f, @mem_int nn (.store arg) :: @const nn c :: @const .double i :: is))
                    (s, (f, @const nn c :: is))
-- todo more
-/

end Memory

inductive Instr : Step
| numeric   : Numeric config config'
            → Instr config config'
| reference : Reference config config'
            → Instr config config'
-- todo vector
| drop      : IsValue val _
            → Instr (s, (f, .real .drop :: val :: is))
                    (s, (f, is))
| select_t  : {c : Unsigned (Numeric.Size.toBits .double)}
            → {_ : IsValue val₁ v₁}
            → {_ : IsValue val₂ v₂}
            → {_ : Value.type v₁ = Value.type v₂}
            → {_ : c ≠ 0}
            → Instr (s, (f, .real (.select t) :: const c :: val₂ :: val₁ :: is))
                    (s, (f, val₁ :: is))
| select_f  : {c : Unsigned (Numeric.Size.toBits .double)}
            → {_ : IsValue val₁ v₁}
            → {_ : IsValue val₂ v₂}
            → {_ : Value.type v₁ = Value.type v₂}
            → {_ : c = 0}
            → Instr (s, (f, .real (.select t) :: const c :: val₂ :: val₁ :: is))
                    (s, (f, val₂ :: is))
| locl      : Local config config'
            → Instr config config'
| globl     : Global config config'
            → Instr config config'
| table     : Table config config'
            → Instr config config'
| elem_drop : {a : Fin (Vec.length s.elems)}
            → {_ : Vec.index s.elems a = f.module.elemaddrs.get x}
            → {_ : elem = s.elems.get a}
            → Instr (s, (f, .real (.elem_drop (Vec.index f.module.elemaddrs x)) :: is))
                    ({s with elems := s.elems.set a {elem with elem := Vec.nil}}, (f, is))
-- todo memory
| nop       : Instr (s, (f, .real .nop :: is))
                    (s, (f, is))
| trap      : Instr (s, (f, .real .unreachable :: is))
                    (s, (f, .admin .trap :: is))
-- todo rest
