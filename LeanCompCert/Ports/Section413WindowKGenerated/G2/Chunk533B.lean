import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533A

def state06 : KState := ⟨⟨360657149126521753, 360657167083552289⟩, ⟨(-4010043951463168043), (-4009396536789391029)⟩, true⟩

def words05 : List Nat := [360582021792604033, 360582022220574190, 360582022998885495, 360582023904966699, 360582024511495084, 360582025118058542, 360582025999748470, 360582027058257482, 360582028467027392, 360582029875913951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611789366656295, 360611807330751572⟩, ⟨(-1589651047907952269), (-1589003256225076457)⟩, true⟩

def words06 : List Nat := [360582030957584493, 360582031689041125, 360582032395827957, 360582033102803443, 360582033611857739, 360582033770805152, 360582033771464688, 360582033754484964, 360582033988017865, 360582034546726070]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578222938151213, 360578240909216658⟩, ⟨201952134970029934, 202600298686068684⟩, true⟩

def words07 : List Nat := [360582035185144647, 360582035823684636, 360582036286269605, 360582036398791134, 360582036399422421, 360582036252924269, 360582036309195462, 360582036413480385, 360582036414146775, 360582036343811752]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591023016521879, 360591040994584882⟩, ⟨(-481297256981715991), (-480648719701647493)⟩, true⟩

def words08 : List Nat := [360582036552455854, 360582037128631753, 360582037617841865, 360582038107170619, 360582038297511949, 360582038298252580, 360582038263869354, 360582038390009859, 360582038395582832, 360582038564967500]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578677539574029, 360578695524688799⟩, ⟨177907566902816956, 178556480711419108⟩, true⟩

def words09 : List Nat := [360582038565630742, 360582038472033914, 360582038560088983, 360582039012913813, 360582039308626422, 360582039604461545, 360582039647217915, 360582039647958731, 360582039340781815, 360582039279009238]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533B
