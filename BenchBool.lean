
abbrev Matrix α m n := Vector (Vector α n) m

@[noinline]
def mmul1 (a : Matrix Bool m n) (x : Vector Bool n) : IO (Vector Bool m) :=
  pure <| Vector.ofFn fun i => Fin.foldl (n := n) (init := false) fun acc j => acc ^^ a[i][j] && x[j]

@[noinline]
def mmul2 (a : Matrix Bool m n) (x : Vector Bool n) : IO (Vector Bool m) :=
  pure <| Vector.ofFn fun i => Fin.foldl (n := n) (init := false) fun acc j => strictXor acc <| strictAnd a[i][j] x[j]

/-- not randomly generated 100 vector -/
@[noinline]
def x [RandomGen G] (size : Nat) : Option G → IO (Vector Bool size × Option G)
  | none => return (.ofFn fun _ => false, none)
  | some g => do
      let mut x : Array Bool := #[]
      let mut g : G := g
      for _ in [:size] do
        let p := randBool g
        x := x.push p.1
        g := p.2
      return (.ofFn fun i => x[i]!, g)

/-- not randomly generated 16×100 matrix -/
@[noinline]
def a [RandomGen G] (size : Nat) (g : Option G) : IO (Matrix Bool size size × Option G) := do
  let mut m : Array (Vector Bool size) := #[]
  let mut g : Option G := g
  for _ in [:size] do
    let p ← x size g
    m := m.push p.1
    g := p.2
  return (.ofFn fun i => m[i]!, g)

def main (args : List String) : IO UInt32 := do
  match args[0]? >>= String.toNat?, args[1]? >>= String.toNat? with
  | none, _ => return 1
  | some size, seed =>
    let g := (mkStdGen ·) <$> seed
    let (a, g) ← a size g
    let (x, _) ← x size g

    let r1 ← timeit "mmul1:" <| mmul1 a x
    let r2 ← timeit "mmul2:" <| mmul2 a x

    -- returns zero iff `r1 = r2`
    return ((Vector.zip r1 r2).any fun (x1, x2) => x1 ^^ x2).toUInt32
