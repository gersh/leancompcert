import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624A

def state06 : KState := ⟨⟨362494959366268353, 362495016749075369⟩, ⟨(-601812179161891220), (-599391269034431668)⟩, true⟩

def words05 : List Nat := [371285420249918448, 371285420147783875, 371285420120391910, 371285420122768336, 371285420164231803, 371285420225299156, 371285420290021255, 371285420292161428, 371285420344447591, 371285420500711840]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478816598003202, 362478873999714640⟩, ⟨406544238537870432, 408966329532739254⟩, true⟩

def words06 : List Nat := [371285420761489190, 371285420763609308, 371285420682902205, 371285420595890951, 371285420508048016, 371285420465210585, 371285420429458077, 371285420541369908, 371285420601162069, 371285420603356913]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505485808663553, 362505543229569089⟩, ⟨(-1259615089473487204), (-1257191799330688270)⟩, true⟩

def words07 : List Nat := [371285420624255003, 371285420751066662, 371285421133073473, 371285421174273697, 371285421175950128, 371285421126717915, 371285421281425250, 371285421395978884, 371285421719470210, 371285422043939367]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493445157934302, 362493502597951933⟩, ⟨(-507252589805525838), (-504828105439348390)⟩, true⟩

def words08 : List Nat := [371285422344978077, 371285422434207185, 371285422778968520, 371285423124796069, 371285423547029802, 371285423655826271, 371285423755761320, 371285423856413373, 371285424053279082, 371285424184973435]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468314342195446, 362468371801313597⟩, ⟨1063306723273975471, 1065732401324332859⟩, true⟩

def words09 : List Nat := [371285424325133168, 371285424466116588, 371285424577931915, 371285424580053229, 371285424350501836, 371285424168346558, 371285424056362732, 371285424058484135, 371285423790200875, 371285423519734787]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624B
