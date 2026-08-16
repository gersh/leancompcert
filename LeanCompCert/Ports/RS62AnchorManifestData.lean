import LeanCompCert.Ports.RS62CheckpointManifestData

/-!
# Literal manifest for the five large RS62 anchor segments

Together with the guarded prefix `[101, 10001)`, these rows cover exactly
`[101, 100000001)`.  The literals are observations to be validated by the
compiled pipeline and compiled configuration receipts, not trusted proofs.
-/

namespace LeanCompCert.Ports.RS62AnchorManifestData

abbrev Row := LeanCompCert.Ports.RS62CheckpointManifestData.Row

def rows : List Row := [
  { idx := 1, fuel := 20007900, lo := 10001, segLen := 19998000,
    rootCap := 4474, mainCount := 607, markSteps := 47838063,
    SL := 191722931109946, SU := 191728806920095,
    lower := 360756559638232, upper := 360762437006569 },
  { idx := 2, fuel := 40005900, lo := 20008001, segLen := 19998000,
    rootCap := 6326, mainCount := 823, markSteps := 48645773,
    SL := 360756559638232, SU := 360762437006569,
    lower := 372123908645052, upper := 372129787176310 },
  { idx := 3, fuel := 60003900, lo := 40006001, segLen := 19998000,
    rootCap := 7747, mainCount := 982, markSteps := 49098872,
    SL := 372123908645052, SU := 372129787176310,
    lower := 378566851826455, upper := 378572731486039 },
  { idx := 4, fuel := 80001900, lo := 60004001, segLen := 19998000,
    rootCap := 8945, mainCount := 1112, markSteps := 49410474,
    SL := 378566851826455, SU := 378572731486039,
    lower := 383051045898099, upper := 383056926664830 },
  { idx := 5, fuel := 99999900, lo := 80002001, segLen := 19998000,
    rootCap := 10000, mainCount := 1229, markSteps := 49658081,
    SL := 383051045898099, SU := 383056926664830,
    lower := 386481147529431, upper := 386487029388140 }
]

theorem rows_length : rows.length = 5 := by rfl

end LeanCompCert.Ports.RS62AnchorManifestData
