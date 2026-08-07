import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504157764757491, 362504235985110629⟩, ⟨(-1378371327632795190), (-1374541508848282392)⟩, true⟩

def state01 : KState := ⟨⟨362494832893506208, 362494911136305806⟩, ⟨(-702327323868897686), (-698495877601365056)⟩, true⟩

def words00 : List Nat := [371285277284251094, 371285277286739873, 371285277429546066, 371285277598135242, 371285277780120280, 371285277804291835, 371285277828494123, 371285277853513738, 371285278036271953, 371285278171961068]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488561795064086, 362488640060331595⟩, ⟨(-247522555485669782), (-243689479958176202)⟩, true⟩

def words01 : List Nat := [371285278461730059, 371285278752558107, 371285279007254422, 371285279080596679, 371285279210831436, 371285279342266404, 371285279639202924, 371285279702035427, 371285279750235932, 371285279799442223]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478718666188501, 362478796953732750⟩, ⟨466419519686096893, 470254210837140745⟩, true⟩

def words02 : List Nat := [371285280007199030, 371285280143254880, 371285280335760122, 371285280529235410, 371285280689206724, 371285280691696246, 371285280598220866, 371285280550601185, 371285280533271119, 371285280535848249]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481203512699514, 362481281822920733⟩, ⟨286225396311594148, 290061732335676944⟩, true⟩

def words03 : List Nat := [371285280448336385, 371285280360522612, 371285280371078004, 371285280421620361, 371285280508348569, 371285280596050201, 371285280683585323, 371285280686075434, 371285280520274374, 371285280468252077]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473970653436290, 362474048985858944⟩, ⟨810937274725579366, 814775221357864838⟩, true⟩

def words04 : List Nat := [371285280414848803, 371285280414683862, 371285280266530563, 371285280119973432, 371285279972443314, 371285279833768441, 371285279612445488, 371285279581941187, 371285279550592038, 371285279519578557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492951689261874, 362493030044216515⟩, ⟨(-566235677851703646), (-562396096409137866)⟩, true⟩

def words05 : List Nat := [371285279401441462, 371285279439411451, 371285279601658707, 371285279604149337, 371285279513594603, 371285279380979277, 371285279247352404, 371285279242664746, 371285279268281024, 371285279377930093]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482750667748536, 362482829045184664⟩, ⟨174003354901689255, 177844567716892063⟩, true⟩

def words06 : List Nat := [371285279469720373, 371285279472255389, 371285279560619604, 371285279691188495, 371285279844673119, 371285279847176125, 371285279819127808, 371285279756899390, 371285279704704757, 371285279707548133]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481092580930036, 362481170980804098⟩, ⟨294373151191142753, 298215992435505667⟩, true⟩

def words07 : List Nat := [371285279800311191, 371285279927829881, 371285280027129603, 371285280029621282, 371285279899146797, 371285279829121094, 371285279874185686, 371285279876694226, 371285279824829921, 371285279771000234]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485231186297346, 362485309608478127⟩, ⟨(-5996404795676890), (-2151944414912702)⟩, true⟩

def words08 : List Nat := [371285279833760305, 371285279858994778, 371285279962859339, 371285280067728813, 371285280143827669, 371285280146319622, 371285279969324251, 371285279935126860, 371285279960654753, 371285279963695511]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484691351211598, 362484769796120113⟩, ⟨33230282156795063, 37076392455927259⟩, true⟩

def words09 : List Nat := [371285279966686738, 371285279970565362, 371285280143463690, 371285280234141448, 371285280381256552, 371285280529299808, 371285280636941432, 371285280639433974, 371285280494130533, 371285280490231077]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725
