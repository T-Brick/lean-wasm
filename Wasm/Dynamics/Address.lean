import Wasm.Syntax
import Numbers

namespace Wasm.Dynamics

open Numbers

def Address := Unsigned32

namespace Address

def Function := Address
def Table    := Address
def Memory   := Address
def Global   := Address
def Element  := Address
def Data     := Address
def Extern   := Address

-- deriving instance Inhabited for Function
-- deriving instance Inhabited for Table
-- deriving instance Inhabited for Memory
-- deriving instance Inhabited for Global
-- deriving instance Inhabited for Element
-- deriving instance Inhabited for Data
-- deriving instance Inhabited for Extern
