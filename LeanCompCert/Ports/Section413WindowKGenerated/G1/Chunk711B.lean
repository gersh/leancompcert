import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711A

def state06 : KState := ⟨⟨362464585098226504, 362464660344498641⟩, ⟨1461942708520418033, 1465558892030569029⟩, true⟩

def words05 : List Nat := [371285257588934114, 371285257308096261, 371285257026242198, 371285256942663495, 371285256772324835, 371285256609552553, 371285256445983729, 371285256283428779, 371285255893557680, 371285255607174732]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476483259879681, 362476558527913016⟩, ⟨615264403909582096, 618882136058253932⟩, true⟩

def words06 : List Nat := [371285255319411205, 371285255229665331, 371285255063839669, 371285254898395048, 371285254732043888, 371285254608670909, 371285254407465206, 371285254404429995, 371285254400568030, 371285254356718106]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500643387997322, 362500718678046503⟩, ⟨(-1104299344251045551), (-1100680045123219579)⟩, true⟩

def words07 : List Nat := [371285254311133291, 371285254388995906, 371285254642622144, 371285254692385846, 371285254732756089, 371285254773944661, 371285254997526345, 371285255123392292, 371285255342298142, 371285255562255447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477583017698849, 362477658329810434⟩, ⟨537178030400208647, 540798900041747567⟩, true⟩

def words08 : List Nat := [371285255743260127, 371285255745699780, 371285255663648678, 371285255665480523, 371285255689767772, 371285255692207522, 371285255454871819, 371285255205435835, 371285254955022523, 371285254886911737]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463741283110240, 362463816617197715⟩, ⟨1522714508451446111, 1526336942667712805⟩, true⟩

def words09 : List Nat := [371285254872163779, 371285254965152445, 371285255050523335, 371285255052963230, 371285254875421057, 371285254735906833, 371285254595180167, 371285254534618406, 371285254232118062, 371285253933808217]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711B
