import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618A

def state06 : KState := ⟨⟨360584723872176022, 360584748293580425⟩, ⟨(-133040709349130926), (-132020158195551382)⟩, true⟩

def words05 : List Nat := [360582611816369155, 360582612116490792, 360582612455707779, 360582612974062240, 360582613384997018, 360582613796060041, 360582614038567966, 360582614080878178, 360582614116092524, 360582614151581500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585299304349341, 360585323733927216⟩, ⟨(-168673429444150984), (-167652372639120820)⟩, true⟩

def words06 : List Nat := [360582614447982474, 360582614484294688, 360582614485069687, 360582614338054715, 360582614190894783, 360582613977227876, 360582614021467819, 360582614082463118, 360582614083236449, 360582614025458966]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603316131092281, 360603340568872793⟩, ⟨(-1283526339632565505), (-1282504775290994481)⟩, true⟩

def words07 : List Nat := [360582614331078329, 360582614636942397, 360582614935663634, 360582614974354445, 360582614975168485, 360582614756781321, 360582614538234592, 360582614557209967, 360582614892850375, 360582615228699057]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601618462488512, 360601642908526927⟩, ⟨(-1178636109157171813), (-1177614033775815893)⟩, true⟩

def words08 : List Nat := [360582615433066603, 360582615433934557, 360582615434661369, 360582615492173243, 360582615492899602, 360582615555252117, 360582615556038952, 360582615423572224, 360582615374272009, 360582615682698038]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565938362817828, 360565962817027413⟩, ⟨1029900063526696560, 1030922644663214164⟩, true⟩

def words09 : List Nat := [360582616166329947, 360582616650112448, 360582616942250765, 360582617241358734, 360582617473708258, 360582617706280290, 360582617848735415, 360582617849603590, 360582617732114442, 360582617463952506]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618B
