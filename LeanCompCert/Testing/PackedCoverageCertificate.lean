import LeanCompCert.Verified.Packed

/-!
# A packed coverage certificate at a scale the functional backends cannot reach

The claim: every integer in `[0, 10 ^ 6)` lies in one of the five residue
classes `0 mod 2`, `0 mod 3`, `1 mod 4`, `5 mod 6`, `7 mod 12` — the
classical covering system.

The point is not the claim, which is elementary, but its *cost*. The
proof below is a single `decide +kernel` over one packed `Nat`: five
`repunit` divisions, four `Nat.lor`s and one `Nat.land`, all inside GMP.
It settles a million cells in well under a second and at no measurable
memory above the elaborator's own footprint.

The same statement decided cell by cell — the shape both `RegState` and
`ArrayState` are forced into — costs seconds at `10 ^ 4` cells and tens
of gigabytes by `10 ^ 5`.

`decide` is used, never `native_decide`: the kernel does this work, and
`#print axioms` on the results below is the base trio.
-/

namespace LeanCompCert.Testing.PackedCoverageCertificate

open LeanCompCert.Verified.Packed

/-- The classical covering system, as `(residue, modulus)` pairs. -/
def coveringSystem : List (Nat × Nat) := [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]

theorem coveringSystem_wf :
    ∀ rm ∈ coveringSystem, 0 < rm.2 ∧ rm.1 < rm.2 := by decide

/-- The number of cells certified in one kernel step. -/
def cells : Nat := 1000000

/-- **The certificate.** One packed acceptance test over `10 ^ 6` cells. -/
theorem coverage_accepted :
    covers (classUnion coveringSystem cells) cells = true := by
  decide +kernel

/-- Every cell below `10 ^ 6` lies in one of the five classes. -/
theorem mem_coveringSystem (i : Nat) (hi : i < cells) :
    ∃ rm ∈ coveringSystem, i % rm.2 = rm.1 :=
  mem_class_of_covers_classUnion coveringSystem cells
    coveringSystem_wf coverage_accepted i hi

/-- Restated without the packed vocabulary: the covering system covers. -/
theorem covering_system_covers (i : Nat) (hi : i < 1000000) :
    i % 2 = 0 ∨ i % 3 = 0 ∨ i % 4 = 1 ∨ i % 6 = 5 ∨ i % 12 = 7 := by
  obtain ⟨rm, hmem, hres⟩ := mem_coveringSystem i hi
  simp only [coveringSystem, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h <;> subst h <;> simp_all

end LeanCompCert.Testing.PackedCoverageCertificate
