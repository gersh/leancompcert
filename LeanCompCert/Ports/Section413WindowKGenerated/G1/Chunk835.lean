import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488092087213092, 362488196981875419⟩, ⟨(-246255867686608886), (-240341750617975622)⟩, true⟩

def state01 : KState := ⟨⟨362491499445411599, 362491604366023132⟩, ⟨(-530789414731604493), (-524873130770113687)⟩, true⟩

def words00 : List Nat := [371285318782232119, 371285318822172596, 371285318909384381, 371285318997785472, 371285319074074052, 371285319076971751, 371285319026976105, 371285319071225080, 371285319209927262, 371285319288239725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488299615123585, 362488404562182437⟩, ⟨(-263529835662056338), (-257611342961248234)⟩, true⟩

def words01 : List Nat := [371285319365448934, 371285319443675178, 371285319623281434, 371285319741831541, 371285319903142689, 371285320065533757, 371285320174263573, 371285320177160706, 371285320131512068, 371285320172113338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476443310032657, 362476548282880016⟩, ⟨726767621776511523, 732688268469578055⟩, true⟩

def words02 : List Nat := [371285320302250875, 371285320305148061, 371285320244445656, 371285320157015320, 371285320068454257, 371285320007291966, 371285319873327607, 371285319863033273, 371285319851754235, 371285319841223960]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499264074973678, 362499369074034825⟩, ⟨(-1179596110839920519), (-1173673274377624849)⟩, true⟩

def words03 : List Nat := [371285319738213677, 371285319695713537, 371285319731832794, 371285319734750103, 371285319688471345, 371285319620017657, 371285319621986450, 371285319663481215, 371285319833622186, 371285320005022273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480276525027737, 362480381550186220⟩, ⟨406691844795984259, 412616861564763303⟩, true⟩

def words04 : List Nat := [371285320175203760, 371285320178101572, 371285320239825449, 371285320326011664, 371285320400377025, 371285320403276456, 371285320312196737, 371285320222027913, 371285320130710668, 371285320112263596]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835
