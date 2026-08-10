import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669A

def state06 : KState := ⟨⟨362482600398456069, 362482666708774481⟩, ⟨187217368436310216, 190216229362439014⟩, true⟩

def words05 : List Nat := [371285507234333969, 371285507318952861, 371285507497393710, 371285507565160434, 371285507642277570, 371285507720223772, 371285507753848190, 371285507756132602, 371285507492473042, 371285507452940587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476467267107516, 362476533597789710⟩, ⟨597957361234243287, 600957585826446353⟩, true⟩

def words06 : List Nat := [371285507535626151, 371285507537950450, 371285507477579141, 371285507393337940, 371285507308245565, 371285507252225118, 371285507111544077, 371285507141952370, 371285507143706567, 371285507131996466]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499099455814012, 362499165807141243⟩, ⟨(-917809882104542225), (-914808274812327587)⟩, true⟩

def words07 : List Nat := [371285507069059208, 371285507141270290, 371285507434994941, 371285507437279962, 371285507434252726, 371285507408228801, 371285507575241310, 371285507667272317, 371285507872746537, 371285508079206272]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480012861432198, 362480079233391273⟩, ⟨360647214092660171, 363650203411471339⟩, true⟩

def words08 : List Nat := [371285508282702614, 371285508284987994, 371285508235530930, 371285508257157201, 371285508345675802, 371285508347961109, 371285508139737108, 371285507930381652, 371285507720130931, 371285507658580279]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466579917609957, 362466646310148362⟩, ⟨1260678371933729677, 1263682739966079595⟩, true⟩

def words09 : List Nat := [371285507684550301, 371285507792508903, 371285507885436840, 371285507887729738, 371285507802511588, 371285507786508554, 371285507783267361, 371285507785553731, 371285507525483881, 371285507246565767]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669B
