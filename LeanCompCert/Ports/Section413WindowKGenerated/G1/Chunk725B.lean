import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725B
