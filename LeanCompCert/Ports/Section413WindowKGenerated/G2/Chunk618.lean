import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585889025957927, 360585913398124948⟩, ⟨(-205412137052152816), (-204394630245713924)⟩, true⟩

def state01 : KState := ⟨⟨360583592376075963, 360583616756415136⟩, ⟨(-63506113589314578), (-62488101702553786)⟩, true⟩

def words00 : List Nat := [360582606270900959, 360582606370403200, 360582606371196733, 360582606270960271, 360582606170585831, 360582605961224398, 360582605914878768, 360582605948857614, 360582605949634849, 360582605802026718]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612986390909165, 360613010779426674⟩, ⟨(-1880511316251276962), (-1879492798820733470)⟩, true⟩

def words01 : List Nat := [360582606027052406, 360582606252336674, 360582606738949424, 360582607072034784, 360582607180029823, 360582607288085361, 360582607389019141, 360582607620236157, 360582608112738344, 360582608605427213]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599936771036736, 360599961167816930⟩, ⟨(-1073837584916058296), (-1072818556646119738)⟩, true⟩

def words02 : List Nat := [360582608967192637, 360582609068430918, 360582609385825892, 360582609703482941, 360582609954902312, 360582610091099904, 360582610091872591, 360582610054091332, 360582610066112114, 360582610347732408]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574582565121110, 360574606970068631⟩, ⟨493872430086164541, 494891963383755755⟩, true⟩

def words03 : List Nat := [360582610474668068, 360582610601748877, 360582610602521219, 360582610598156839, 360582610430885906, 360582610159348051, 360582609887564578, 360582609878583711, 360582609879363323, 360582609750847800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610267041792195, 360610291454927819⟩, ⟨(-1713051920799878057), (-1712031881110497269)⟩, true⟩

def words04 : List Nat := [360582609622143406, 360582609537283600, 360582609857378925, 360582610177630142, 360582610287710019, 360582610340139325, 360582610513913993, 360582610687945447, 360582611067915471, 360582611516347837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618
