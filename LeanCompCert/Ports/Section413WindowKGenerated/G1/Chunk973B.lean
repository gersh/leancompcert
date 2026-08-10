import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973A

def state06 : KState := ⟨⟨362470918558830973, 362471062866342163⟩, ⟨1380360895433148299, 1389846635482714367⟩, true⟩

def words05 : List Nat := [371285338535208253, 371285338599061549, 371285338651985256, 371285338655401886, 371285338567496934, 371285338513170520, 371285338467988716, 371285338471405615, 371285338344286368, 371285338201546382]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477583162033270, 362477727500151412⟩, ⟨731433058281034557, 740921778380960213⟩, true⟩

def words06 : List Nat := [371285338057256790, 371285337955645539, 371285337800499946, 371285337689252027, 371285337576972298, 371285337449281659, 371285337191548984, 371285337041173392, 371285336888996959, 371285336843669754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479399709711351, 362479544078941544⟩, ⟨554559632761813971, 564051382399870965⟩, true⟩

def words07 : List Nat := [371285336768101792, 371285336692721572, 371285336642416679, 371285336646183167, 371285336622435268, 371285336611760152, 371285336599916115, 371285336568221442, 371285336405520322, 371285336350274466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480984862696452, 362481129262345219⟩, ⟨400216213488526121, 409710925445570199⟩, true⟩

def words08 : List Nat := [371285336339162741, 371285336342589067, 371285336308200226, 371285336251550869, 371285336193493326, 371285336168615434, 371285336113960469, 371285336141912011, 371285336168401296, 371285336171940102]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498239399161651, 362498383829803871⟩, ⟨(-1280316542225195008), (-1270818811659300338)⟩, true⟩

def words09 : List Nat := [371285336131690443, 371285336136416643, 371285336201996455, 371285336205445589, 371285336199208837, 371285336174547058, 371285336225643236, 371285336268586276, 371285336404862489, 371285336542695327]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973B
