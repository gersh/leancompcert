import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919A

def state06 : KState := ⟨⟨362471157946125916, 362471286123596073⟩, ⟨1262184259391787459, 1270142685391400295⟩, true⟩

def words05 : List Nat := [371285098409731800, 371285098456359891, 371285098484642577, 371285098487861742, 371285098388366535, 371285098315979621, 371285098283960084, 371285098287174785, 371285098174048078, 371285098027525950]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492007914475884, 362492136120715887⟩, ⟨(-655267708291647402), (-647306636471364040)⟩, true⟩

def words06 : List Nat := [371285097879512776, 371285097851104524, 371285097792353210, 371285097810103787, 371285097812591441, 371285097811335950, 371285097725848505, 371285097744997467, 371285097880600275, 371285097960464598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481803654791667, 362481931890350107⟩, ⟨283281645204709244, 291245413587377854⟩, true⟩

def words07 : List Nat := [371285098014692884, 371285098069937824, 371285098172566174, 371285098217564767, 371285098285500753, 371285098354682348, 371285098414641599, 371285098417856947, 371285098320085800, 371285098289715050]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475588920308028, 362475717184486803⟩, ⟨854990203918091648, 862956604949183838⟩, true⟩

def words08 : List Nat := [371285098319941973, 371285098323181275, 371285098302668790, 371285098283072717, 371285098275321536, 371285098278865470, 371285098235261056, 371285098213363115, 371285098190413160, 371285098167256117]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496905271364920, 362497033564636670⟩, ⟨(-1106023213863705509), (-1098054136424235371)⟩, true⟩

def words09 : List Nat := [371285098067459912, 371285098069013009, 371285098126870642, 371285098130142769, 371285098092300306, 371285098036641787, 371285098038681251, 371285098058004135, 371285098189918677, 371285098323319465]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919B
