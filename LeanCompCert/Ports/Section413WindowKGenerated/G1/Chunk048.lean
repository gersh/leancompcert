import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk048

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362394075186240685, 362394075456588285⟩, ⟨429630469870563631, 429631349447455531⟩, true⟩

def state01 : KState := ⟨⟨362287578782099264, 362287579053618189⟩, ⟨942295691352304093, 942296576557700337⟩, true⟩

def words00 : List Nat := [371283587771486355, 371283587771619831, 371283576057195168, 371283564489482360, 371283552926535947, 371283552783150000, 371283532047196980, 371283519057039523, 371283506072241337, 371283482707788190]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362685145460850376, 362685145733557701⟩, ⟨(-972131761510878772), (-972130870583163998)⟩, true⟩

def words01 : List Nat := [371283441987933309, 371283428254966649, 371283443659334474, 371283443659466234, 371283429468349305, 371283408325882001, 371283408878639867, 371283416978271970, 371283458830800631, 371283500666023339]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362377331572877627, 362377331846777920⟩, ⟨512302869066710322, 512303765750599306⟩, true⟩

def words02 : List Nat := [371283542682715305, 371283542682847237, 371283527682394145, 371283520575579341, 371283519565684697, 371283519565816988, 371283483746024932, 371283448182671469, 371283412633995429, 371283398879024421]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362233068031284684, 362233068306378419⟩, ⟨1210849995363691360, 1210850897818010556⟩, true⟩

def words03 : List Nat := [371283397510320668, 371283418088655062, 371283438329889464, 371283438330021916, 371283401844142077, 371283377849782224, 371283353865277965, 371283347823174546, 371283295811459804, 371283244111712719]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362278722655564577, 362278722931847126⟩, ⟨990342461171696216, 990343369385984462⟩, true⟩

def words04 : List Nat := [371283192433264510, 371283173515726087, 371283134195938091, 371283124271979755, 371283114352076456, 371283095998174933, 371283021271537505, 371282977551166653, 371282933848759364, 371282917440998876]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362305512144402919, 362305512421897489⟩, ⟨860020008224070103, 860020922322915429⟩, true⟩

def words05 : List Nat := [371282875347820171, 371282818854686223, 371282762384781913, 371282734882985938, 371282686101617111, 371282649994904851, 371282613903015081, 371282578279435705, 371282507878066361, 371282471459412493]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362347552405411097, 362347552684093849⟩, ⟨656468883310400883, 656469803190056533⟩, true⟩

def words06 : List Nat := [371282440520284136, 371282440520419209, 371282426382145389, 371282412753156687, 371282399129719960, 371282386856766600, 371282353332690558, 371282352986747117, 371282352640903434, 371282351411648276]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474064986200443, 362474065266094563⟩, ⟨40350614202097793, 40351539987236773⟩, true⟩

def words07 : List Nat := [371282337766633102, 371282351789660022, 371282387600016951, 371282387600150601, 371282367722533079, 371282343957663417, 371282338035423830, 371282338035572250, 371282335718902097, 371282334024288669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362397752606224966, 362397752887326617⟩, ⟨412221369014033159, 412222300698184391⟩, true⟩

def words08 : List Nat := [371282332330318448, 371282331121106783, 371282274409187572, 371282247269414723, 371282220140688395, 371282205519985222, 371282156618559605, 371282107914298688, 371282059229906098, 371282051926324201]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362159880383311886, 362159880665623740⟩, ⟨1577311972278523095, 1577312909886671259⟩, true⟩

def words09 : List Nat := [371282050456478438, 371282066215783942, 371282072527062099, 371282072527196388, 371282023617009104, 371281974417539118, 371281925238090601, 371281907984930798, 371281846966734560, 371281781259478163]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk048
