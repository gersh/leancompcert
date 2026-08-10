import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859A

def state06 : KState := ⟨⟨362471434937894357, 362471546353520515⟩, ⟨1172151665254884395, 1178618346194409427⟩, true⟩

def words05 : List Nat := [371285258179523654, 371285258197658543, 371285258199931083, 371285258191883959, 371285258061563381, 371285257974280117, 371285257905975004, 371285257908963331, 371285257751398131, 371285257595332921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466900549165392, 362467011991528293⟩, ⟨1562005998716157540, 1568474978083362270⟩, true⟩

def words06 : List Nat := [371285257437854338, 371285257396599528, 371285257286503217, 371285257254810317, 371285257222230448, 371285257149886511, 371285256915313124, 371285256738365361, 371285256559809055, 371285256437010245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470212338730380, 362470323808268548⟩, ⟨1277295855149176596, 1283767170914537380⟩, true⟩

def words07 : List Nat := [371285256227028005, 371285256018107848, 371285255808003040, 371285255716794078, 371285255584457204, 371285255485439974, 371285255385388648, 371285255271212220, 371285254975825606, 371285254805836757]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458640794804495, 362458752291012109⟩, ⟨2272283892520436843, 2278757501463233849⟩, true⟩

def words08 : List Nat := [371285254634245110, 371285254506744580, 371285254249029466, 371285253992460981, 371285253734712766, 371285253499515760, 371285253209950039, 371285252991233203, 371285252771480627, 371285252552687458]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486103435342265, 362486214958597911⟩, ⟨(-89360137335722623), (-82884202399275891)⟩, true⟩

def words09 : List Nat := [371285252246540022, 371285252077023746, 371285251905934140, 371285251862666005, 371285251711920232, 371285251541214574, 371285251369325756, 371285251295974035, 371285251185397252, 371285251200009066]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859B
