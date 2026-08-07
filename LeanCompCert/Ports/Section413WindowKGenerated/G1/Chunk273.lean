import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk273

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492649057589038, 362492659303118466⟩, ⟨(-199017168230698509), (-198828085098968951)⟩, true⟩

def state01 : KState := ⟨⟨362476457121899394, 362476467375156802⟩, ⟨243248665292389293, 243437959438357039⟩, true⟩

def words00 : List Nat := [371285377714274505, 371285378126326411, 371285378515145950, 371285378904235435, 371285379574247112, 371285379668423211, 371285380196686986, 371285380725245956, 371285381250473243, 371285381251372048]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519035159806204, 362519045420921003⟩, ⟨(-919768851418811209), (-919579342647135861)⟩, true⟩

def words01 : List Nat := [371285381702947791, 371285382481310176, 371285383639292209, 371285383687465358, 371285383688144257, 371285383507834525, 371285384236998448, 371285384621269697, 371285385853955195, 371285387086941752]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362509480301604940, 362509490570578853⟩, ⟨(-658825774121269254), (-658636050599320698)⟩, true⟩

def words02 : List Nat := [371285388054687833, 371285388055558752, 371285388401373608, 371285389146565621, 371285390307421316, 371285390308294534, 371285390196175392, 371285390081836786, 371285391189763814, 371285392072514409]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481579211713402, 362481589488497177⟩, ⟨104009793197344577, 104199730203657181⟩, true⟩

def words03 : List Nat := [371285394126774481, 371285396181228751, 371285398236745052, 371285398734506841, 371285399048112347, 371285399362118957, 371285401012751922, 371285401013621510, 371285400882613323, 371285400744173975]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491826823472149, 362491837108053246⟩, ⟨(-176023978447451962), (-175833828223308914)⟩, true⟩

def words04 : List Nat := [371285401428606687, 371285401816230401, 371285403229131437, 371285404642292599, 371285405846636524, 371285405946263704, 371285406473399410, 371285407000935167, 371285408082354093, 371285408318311617]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487206507386905, 362487216799914896⟩, ⟨(-49575463651496099), (-49385096041438515)⟩, true⟩

def words05 : List Nat := [371285408542077676, 371285408766125452, 371285409838198226, 371285410353520545, 371285411270574860, 371285412187902499, 371285412844016978, 371285412844887224, 371285411787992963, 371285411855064875]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482399061242892, 362482409361531758⟩, ⟨81962595875954200, 82153175864492138⟩, true⟩

def words06 : List Nat := [371285413256046740, 371285413256917055, 371285412879515532, 371285412238811059, 371285411597832001, 371285411197018290, 371285410398761773, 371285410667345849, 371285410938100287, 371285410939020414]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502807301072936, 362502817609222393⟩, ⟨(-476614091958752786), (-476423296786122710)⟩, true⟩

def words07 : List Nat := [371285411833447276, 371285412837903451, 371285414943790209, 371285415272977606, 371285415444446579, 371285415616184722, 371285416340878301, 371285416559524277, 371285417195659872, 371285417832121991]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471577240378553, 362471587556381796⟩, ⟨378499860826250189, 378690871075602331⟩, true⟩

def words08 : List Nat := [371285418465023234, 371285418465894275, 371285417407563972, 371285417493236273, 371285417979747733, 371285417980618853, 371285416692042042, 371285415231047343, 371285413769813842, 371285413437034429]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451110055948066, 362451120379814259⟩, ⟨939165435561383521, 939356661216896429⟩, true⟩

def words09 : List Nat := [371285412932879887, 371285412676533242, 371285412419900824, 371285412041662304, 371285409889146219, 371285408138619106, 371285406387769957, 371285405967855293, 371285404719905547, 371285403469639694]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk273
