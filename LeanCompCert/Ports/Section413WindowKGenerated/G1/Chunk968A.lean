import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511940268517584, 362512082857642300⟩, ⟨(-2600757558157858888), (-2591438639709848176)⟩, true⟩

def state01 : KState := ⟨⟨362499974233284548, 362500116853042654⟩, ⟨(-1442428962365984391), (-1433107078446090543)⟩, true⟩

def words00 : List Nat := [371285312343577443, 371285312498742581, 371285312697042196, 371285312897060781, 371285313120203779, 371285313213509267, 371285313294167233, 371285313375997709, 371285313553175919, 371285313710027438]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479137480376664, 362479280130646178⟩, ⟨574913911643731981, 584238749531991763⟩, true⟩

def words01 : List Nat := [371285313898852072, 371285314088998646, 371285314276133977, 371285314321828430, 371285314370214995, 371285314420321156, 371285314512846794, 371285314516243232, 371285314466706187, 371285314408166649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493861914841802, 362494004595518432⟩, ⟨(-850743201853466946), (-841415419796988572)⟩, true⟩

def words02 : List Nat := [371285314392641910, 371285314404854114, 371285314522378138, 371285314641406049, 371285314741469695, 371285314744866325, 371285314764366727, 371285314830397982, 371285314977003481, 371285315070265187]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495011982444279, 362495154694172332⟩, ⟨(-962129435521248503), (-952798646602898035)⟩, true⟩

def words03 : List Nat := [371285315136619508, 371285315204108461, 371285315324592746, 371285315393389734, 371285315489328664, 371285315586538593, 371285315682346989, 371285315690422262, 371285315794325945, 371285315900204871]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492328124866138, 362492470866841424⟩, ⟨(-702199582079412944), (-692865863863016218)⟩, true⟩

def words04 : List Nat := [371285316103448414, 371285316183817941, 371285316261210773, 371285316339742536, 371285316423120256, 371285316454721212, 371285316591647949, 371285316730000598, 371285316853350855, 371285316930755447]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968A
