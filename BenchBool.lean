
abbrev Matrix α m n := Vector (Vector α n) m

@[noinline]
def mmul1 (a : Matrix Bool m n) (x : Vector Bool n) : IO (Vector Bool m) :=
  pure <| Vector.ofFn fun i => Fin.foldl (n := n) (init := false) fun acc j => acc ^^ a[i][j] && x[j]

@[noinline]
def mmul2 (a : Matrix Bool m n) (x : Vector Bool n) : IO (Vector Bool m) :=
  pure <| Vector.ofFn fun i => Fin.foldl (n := n) (init := false) fun acc j => strictXor acc <| strictAnd a[i][j] x[j]

/-- not randomly generated 16×100 matrix -/
def a (size : Nat) : Matrix Bool size size := .ofFn fun _ => .ofFn fun _ => false

/-- not randomly generated 100 vector -/
def x (size : Nat) : Vector Bool size := .ofFn fun _ => false

def main : IO UInt32 := do
  let a := a 10000
  let x := x 10000

  let r1 ← timeit "mmul1:" <| mmul1 a x
  let r2 ← timeit "mmul2:" <| mmul2 a x

  -- returns zero iff `r1 = r2`
  return ((Vector.zip r1 r2).any fun (x1, x2) => x1 ^^ x2).toUInt32
