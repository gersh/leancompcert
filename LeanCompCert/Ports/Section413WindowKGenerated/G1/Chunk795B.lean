import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795A

def state06 : KState := ⟨⟨362479676841648548, 362479771717922653⟩, ⟨426986131250523918, 432083275894136724⟩, true⟩

def words05 : List Nat := [371285202916972206, 371285202896600001, 371285202942345440, 371285202945374573, 371285202935650988, 371285202933678592, 371285202930805665, 371285202917911437, 371285202693655106, 371285202628881604]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479850879606951, 362479945780374103⟩, ⟨413177081544604256, 418276174984876306⟩, true⟩

def words06 : List Nat := [371285202652074093, 371285202654871009, 371285202615349978, 371285202547330008, 371285202478283453, 371285202458803277, 371285202413653485, 371285202465954333, 371285202484514704, 371285202487361472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497753727019537, 362497848652619603⟩, ⟨(-1011439065453304771), (-1006337995933625835)⟩, true⟩

def words07 : List Nat := [371285202491162882, 371285202562428103, 371285202736766629, 371285202770346565, 371285202778941154, 371285202788470055, 371285202870163449, 371285202874355415, 371285203035126678, 371285203197097134]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482101444553053, 362482196394988188⟩, ⟨234179929083664896, 239282975106058220⟩, true⟩

def words08 : List Nat := [371285203345330920, 371285203348080762, 371285203287060998, 371285203291656488, 371285203300124651, 371285203302887776, 371285203160466623, 371285203001417633, 371285202841277841, 371285202840208770]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466217630690752, 362466312605915806⟩, ⟨1498504450614435598, 1503609469790428932⟩, true⟩

def words09 : List Nat := [371285202845358139, 371285202889419737, 371285202926818550, 371285202929576516, 371285202805235594, 371285202730724391, 371285202654795025, 371285202636026685, 371285202406296832, 371285202172119204]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795B
