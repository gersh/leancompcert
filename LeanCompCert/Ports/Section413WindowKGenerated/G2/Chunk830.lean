import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603407112004548, 360603452111628621⟩, ⟨(-1748527296955596052), (-1746004894937364488)⟩, true⟩

def state01 : KState := ⟨⟨360614616679304022, 360614661690256174⟩, ⟨(-2679095204639312570), (-2676571862333706936)⟩, true⟩

def words00 : List Nat := [360582416335137628, 360582416411741944, 360582416633206247, 360582416855014801, 360582416995829437, 360582417210331701, 360582417331846316, 360582417453476274, 360582417719950736, 360582418109738729]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584052706877254, 360584097729058084⟩, ⟨(-141850951242770364), (-139326676788354880)⟩, true⟩

def words01 : List Nat := [360582418480520765, 360582418851517281, 360582419090841151, 360582419185548784, 360582419243542081, 360582419301862027, 360582419381989293, 360582419476261165, 360582419497536934, 360582419519005347]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602158523420485, 360602203556836355⟩, ⟨(-1645064782659072033), (-1642539575419480083)⟩, true⟩

def words02 : List Nat := [360582419642156052, 360582419853998812, 360582420210505485, 360582420567231734, 360582420790701750, 360582420869547708, 360582420900533177, 360582420931863114, 360582421072455676, 360582421311946863]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591404870136573, 360591449914886781⟩, ⟨(-752099957474465005), (-749573809087516351)⟩, true⟩

def words03 : List Nat := [360582421459326890, 360582421606828313, 360582421846468015, 360582422196927811, 360582422510551286, 360582422824361474, 360582423056602487, 360582423144304502, 360582423253977585, 360582423364037352]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584437444121616, 360584482500103459⟩, ⟨(-173580658905574993), (-171053577787055575)⟩, true⟩

def words04 : List Nat := [360582423469812635, 360582423471003501, 360582423432211578, 360582423320936869, 360582423209467683, 360582423012866252, 360582422907966561, 360582422928714610, 360582422929779219, 360582422879174307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360599134909105196, 360599179976318199⟩, ⟨(-1394321941370480665), (-1391793927448262191)⟩, true⟩

def words05 : List Nat := [360582423005419610, 360582423132024927, 360582423310417303, 360582423377164601, 360582423378282678, 360582423313435859, 360582423248365989, 360582423283968892, 360582423486673809, 360582423689643969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598954531907732, 360598999610492676⟩, ⟨(-1379367991227671286), (-1376839032697298738)⟩, true⟩

def words06 : List Nat := [360582423781699367, 360582423940627154, 360582424244174156, 360582424548063692, 360582424783174343, 360582424934391623, 360582425012703623, 360582425091146175, 360582425165480029, 360582425366379842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584806571406138, 360584851661207063⟩, ⟨(-203954226855313192), (-201424336558304118)⟩, true⟩

def words07 : List Nat := [360582425711707500, 360582426057263402, 360582426329922190, 360582426498896245, 360582426629597546, 360582426760635752, 360582427036123678, 360582427167310308, 360582427197568293, 360582427227984566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595739827708870, 360595784928769703⟩, ⟨(-1112390416087375311), (-1109859590261434063)⟩, true⟩

def words08 : List Nat := [360582427374637440, 360582427613173494, 360582427737423074, 360582427861869719, 360582427862969667, 360582427860739671, 360582427713776368, 360582427631172652, 360582427609061698, 360582427771071981]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592247520535214, 360592292632941160⟩, ⟨(-822156981438836919), (-819625212890799899)⟩, true⟩

def words09 : List Nat := [360582427860186575, 360582427949428946, 360582428183206022, 360582428527994470, 360582428836014782, 360582429144231411, 360582429340626292, 360582429392635412, 360582429512291370, 360582429632340797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830
