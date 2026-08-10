import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835A

def state06 : KState := ⟨⟨362468662853337713, 362468767904665092⟩, ⟨1377114358639881520, 1383041561952800792⟩, true⟩

def words05 : List Nat := [371285320091342837, 371285320130796434, 371285320169026607, 371285320171924651, 371285320019136372, 371285319879691796, 371285319738997280, 371285319741896686, 371285319578184837, 371285319383386404]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487336221622986, 362487441298888766⟩, ⟨(-183282527054071459), (-177353156194899509)⟩, true⟩

def words06 : List Nat := [371285319187275335, 371285319135598759, 371285319062332704, 371285319099446146, 371285319113312244, 371285319116262429, 371285319033709853, 371285319007650618, 371285319085091486, 371285319113487193]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493353445648711, 362493458549333414⟩, ⟨(-686194820828595273), (-680263242005955813)⟩, true⟩

def words07 : List Nat := [371285319138016930, 371285319163507299, 371285319246918139, 371285319260123507, 371285319314163630, 371285319369339168, 371285319421930894, 371285319424852382, 371285319478447302, 371285319579447843]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479429855679497, 362479534985173346⟩, ⟨477635155019993170, 483568891105902064⟩, true⟩

def words08 : List Nat := [371285319762369749, 371285319803467156, 371285319828634892, 371285319854801733, 371285319913197675, 371285319916392992, 371285319947224129, 371285319994280429, 371285319996468582, 371285319994039310]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505768265310683, 362505873421048638⟩, ⟨(-1724108457855493110), (-1718172527897800664)⟩, true⟩

def words09 : List Nat := [371285320000691843, 371285320078116420, 371285320287365448, 371285320379002975, 371285320446924947, 371285320515722131, 371285320726441787, 371285320866941077, 371285321114752461, 371285321363921358]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835B
