import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk772

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575264046704599, 360575302757413498⟩, ⟨527893188735419911, 529911613719459619⟩, true⟩

def state01 : KState := ⟨⟨360581160877224666, 360581199598340876⟩, ⟨72642528870313000, 74661757352620632⟩, true⟩

def words00 : List Nat := [360582166888032495, 360582167051412517, 360582167158296335, 360582167265372481, 360582167266388505, 360582167230270267, 360582167026685450, 360582166873790869, 360582166720583002, 360582166594291565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576118327058623, 360576157058679209⟩, ⟨462032181706466809, 464052221281111333⟩, true⟩

def words01 : List Nat := [360582166582759722, 360582166462358452, 360582166387680367, 360582166552311361, 360582166674684030, 360582166797235633, 360582166798234385, 360582166791584322, 360582166617493909, 360582166540954282]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566727132598291, 360566765874579456⟩, ⟨1187210151511037131, 1189230991182871039⟩, true⟩

def words02 : List Nat := [360582166464024424, 360582166410889562, 360582166190414639, 360582165886306972, 360582165582009083, 360582165234896771, 360582164988888397, 360582164833266635, 360582164677537570, 360582164437199978]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580305878685240, 360580344631086166⟩, ⟨138304712737088487, 140326357177763937⟩, true⟩

def words03 : List Nat := [360582164238732050, 360582163894414502, 360582163549786737, 360582163248596665, 360582162898838375, 360582162410468017, 360582161921899262, 360582161601013274, 360582161411068495, 360582161388688157]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589884084170134, 360589922847062721⟩, ⟨(-601661994836399655), (-599639539967979921)⟩, true⟩

def words04 : List Nat := [360582161366149565, 360582161260012663, 360582161164326726, 360582161200900824, 360582161201839408, 360582161122522592, 360582160993006683, 360582160780567777, 360582160567920171, 360582160623402601]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564643275762894, 360564682049053619⟩, ⟨1348396670185036489, 1350419928361276707⟩, true⟩

def words05 : List Nat := [360582160844533416, 360582161065889630, 360582161158910854, 360582161197899519, 360582161198822150, 360582161196013536, 360582161266726432, 360582161267828812, 360582161175630335, 360582160950533833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360614627072583472, 360614665856272614⟩, ⟨(-2513595477864886447), (-2511571416255399805)⟩, true⟩

def words06 : List Nat := [360582160725193341, 360582160708824124, 360582160918351877, 360582161128092788, 360582161169003714, 360582161214407433, 360582161426778040, 360582161639467163, 360582162019020848, 360582162440809434]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594079147071118, 360594117941279027⟩, ⟨(-925789843856831761), (-923764969411842333)⟩, true⟩

def words07 : List Nat := [360582162760098774, 360582163079504886, 360582163333466790, 360582163681474764, 360582163920586670, 360582164159864841, 360582164315346704, 360582164316449329, 360582164459544584, 360582164615501516]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589618158433818, 360589656963020970⟩, ⟨(-581018475736458286), (-578992799131277972)⟩, true⟩

def words08 : List Nat := [360582164907387536, 360582165143806476, 360582165286434919, 360582165429169876, 360582165437540134, 360582165573610438, 360582165672989254, 360582165772560970, 360582165788387916, 360582165886451496]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614081554730771, 360614120369729943⟩, ⟨(-2471897070557929196), (-2469870589156265868)⟩, true⟩

def words09 : List Nat := [360582166151362804, 360582166416604996, 360582166778615776, 360582167145190221, 360582167368791817, 360582167592473290, 360582167842570491, 360582168200275740, 360582168614522702, 360582169029007880]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk772
