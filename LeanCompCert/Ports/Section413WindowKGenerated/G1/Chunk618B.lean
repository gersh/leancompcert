import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618A

def state06 : KState := ⟨⟨362487045714941043, 362487101957725260⟩, ⟨(-108638673304286429), (-106288627742526683)⟩, true⟩

def words05 : List Nat := [371285382376876088, 371285382538698846, 371285382832455165, 371285383034410853, 371285383291598920, 371285383549611283, 371285383791370538, 371285383793468949, 371285383742610176, 371285383772960344]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480011389666175, 362480067651144617⟩, ⟨326565081146815074, 328916283229462814⟩, true⟩

def words06 : List Nat := [371285384063712075, 371285384065810576, 371285384008377345, 371285383919292680, 371285383829367226, 371285383818980904, 371285383781589828, 371285383850419081, 371285383897283799, 371285383899459301]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497717733045698, 362497774013544626⟩, ⟨(-769026433161142029), (-766674054188433305)⟩, true⟩

def words07 : List Nat := [371285383990501219, 371285384168577744, 371285384453421826, 371285384455520695, 371285384392370487, 371285384251009513, 371285384177715745, 371285384180028522, 371285384320510807, 371285384523164891]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489558881266230, 362489615180687720⟩, ⟨(-264181251646091015), (-261827701648068189)⟩, true⟩

def words08 : List Nat := [371285384723911092, 371285384726010161, 371285384619124562, 371285384662249178, 371285384783003731, 371285384785119116, 371285384729236660, 371285384619793893, 371285384645062817, 371285384715811598]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474481859532052, 362474538177821121⟩, ⟨669106043127075922, 671460760938300708⟩, true⟩

def words09 : List Nat := [371285384998694692, 371285385282403302, 371285385544426435, 371285385590402660, 371285385714439119, 371285385839527807, 371285386022087517, 371285386024187150, 371285385858979358, 371285385686075375]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618B
