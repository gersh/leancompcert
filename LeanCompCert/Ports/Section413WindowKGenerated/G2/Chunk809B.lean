import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809A

def state06 : KState := ⟨⟨360622084224727374, 360622126956720356⟩, ⟨(-3237682572186602999), (-3235346080690481055)⟩, true⟩

def words05 : List Nat := [360582161926214766, 360582162192092021, 360582162610017360, 360582162976929149, 360582163197993498, 360582163419114206, 360582163755422662, 360582164182296405, 360582164676846436, 360582165171654825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613532822453962, 360613575565486290⟩, ⟨(-2545331216112931087), (-2542993830815840483)⟩, true⟩

def words06 : List Nat := [360582165590051732, 360582166012551037, 360582166587148540, 360582167162090199, 360582167698669383, 360582168083253327, 360582168385208931, 360582168687284409, 360582168946518118, 360582169335714942]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576665831548833, 360576708585494892⟩, ⟨439965270050767344, 442303539087997340⟩, true⟩

def words07 : List Nat := [360582169675320214, 360582170015131123, 360582170278480280, 360582170389785438, 360582170420281384, 360582170451104424, 360582170526939654, 360582170536844204, 360582170537876804, 360582170471628358]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600971953533450, 360601014718438480⟩, ⟨(-1528523806461909907), (-1526184649914558245)⟩, true⟩

def words08 : List Nat := [360582170442657495, 360582170597933390, 360582170703805612, 360582170809879876, 360582170810948912, 360582170786533544, 360582170609788336, 360582170557973164, 360582170604976774, 360582170838872670]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580509807245429, 360580552583191665⟩, ⟨128802643377197460, 131142694205383144⟩, true⟩

def words09 : List Nat := [360582170995862773, 360582171152965707, 360582171284586896, 360582171492787731, 360582171633651757, 360582171774701345, 360582171786584796, 360582171787744061, 360582171647449848, 360582171628799139]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809B
