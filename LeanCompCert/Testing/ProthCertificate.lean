import LeanCompCert.Ports.TGProth

/-!
# A Proth-test certificate artifact

`N = 274877906947·2⁵² + 1 = 1237940039298891073781235713` is a 91-bit Proth
prime — the scale the Helfgott–Platt ladder actually runs at — and `3` is
its smallest quadratic non-residue witness.  The emitted artifact evaluates
`3^((N−1)/2) mod N` entirely in 64-bit registers, by Montgomery
multiplication, with no division anywhere, and exits `0` exactly when the
result is `N − 1`.

This is the certificate form of `bench/TGProthEmit.lean`, wired into
`lean-compcert check-native` so the artifact is compiled with CompCert and
run on every acceptance pass.  As everywhere in this package the run is
corroboration, never a premise.
-/

namespace LeanCompCert.Testing.ProthCertificate

open LeanCompCert.Ports.TGProth

/-- Proth exponent of the reference producer. -/
def n : Nat := 52
/-- Width of the `k` window: `k < 2³⁹` covers the ladder to `10²⁷`. -/
def kbits : Nat := 39
/-- A real ladder-scale Proth prime's `k`. -/
def k : Nat := 274877906947
/-- Its smallest Proth witness. -/
def a : Nat := 3

/-- `N = k·2ⁿ + 1`, 91 bits. -/
def N : Nat := prothN n k

def program : LeanCompCert.Verified.Reflect.Program := prothProgram n kbits k a

private def mainC (name : String) : String :=
  "\nint main(void)\n{\n    return l_" ++ name ++
    "() == UINT64_C(0) ? 0 : 1;\n}\n"

/-- The artifact: rolled C plus the exit-code wrapper. -/
def emittedC : Except (Array String) String :=
  match emitProth n kbits k a "ProthCertificate" with
  | .error errs => .error errs
  | .ok source => .ok (source ++ mainC "ProthCertificate")

end LeanCompCert.Testing.ProthCertificate
