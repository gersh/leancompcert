import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk279

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360561815479963902, 360561820132646534⟩, ⟨574648654948458814, 574736454645119218⟩, true⟩

def state01 : KState := ⟨⟨360557177380284429, 360557182036430207⟩, ⟨704246090956152925, 704333987292585027⟩, true⟩

def words00 : List Nat := [360582419810203161, 360582420406548700, 360582420406876270, 360582420215590638, 360582420024258798, 360582419636092182, 360582419636391763, 360582419401654260, 360582419166902137, 360582417937085621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360635449290468621, 360635453950086227⟩, ⟨(-1480996525945510245), (-1480908532693341613)⟩, true⟩

def words01 : List Nat := [360582417033229050, 360582415924323849, 360582414815390674, 360582414627947671, 360582414046183647, 360582412368371765, 360582410690603551, 360582410913028018, 360582412813147842, 360582414713214577]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564291312182590, 360564295975308819⟩, ⟨505849181922340568, 505937273151934838⟩, true⟩

def words02 : List Nat := [360582415758895839, 360582416251692005, 360582416707954104, 360582417164287842, 360582417292685235, 360582417293053196, 360582416144147643, 360582414183934801, 360582412223794031, 360582410449821957]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360427673903907894, 360427678570498472⟩, ⟨4322351796524207039, 4322439984530650987⟩, true⟩

def words03 : List Nat := [360582409801577034, 360582408984823127, 360582408168087621, 360582406708274257, 360582403971737059, 360582400578316850, 360582397185034868, 360582393228437509, 360582388473280143, 360582382936444451]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360533651264606986, 360533655934671512⟩, ⟨1360860897587266651, 1360949182672881091⟩, true⟩

def words04 : List Nat := [360582377399919551, 360582373141679895, 360582369528293596, 360582367192932676, 360582364857707761, 360582361328082834, 360582356955723707, 360582353861202200, 360582350766794127, 360582348213121347]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360553759686383187, 360553764359956583⟩, ⟨798616262393203644, 798704645569492830⟩, true⟩

def words05 : List Nat := [360582346471398761, 360582343537779061, 360582340604298949, 360582338948012395, 360582337936915644, 360582336599682601, 360582335262504802, 360582333283138988, 360582331355694531, 360582330334404706]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593945664737536, 360593950341779557⟩, ⟨(-325122394612089983), (-325033914435686451)⟩, true⟩

def words06 : List Nat := [360582329567501534, 360582330223272330, 360582330223605114, 360582330046953403, 360582329870260579, 360582328515479495, 360582328708752196, 360582329443316533, 360582329536448823, 360582329952289168]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611705957417100, 360611710637942827⟩, ⟨(-821973511264315991), (-821884933631775403)⟩, true⟩

def words07 : List Nat := [360582331287359776, 360582332622453871, 360582334143441278, 360582334819268516, 360582334819608692, 360582334393601616, 360582334448393861, 360582335572615515, 360582336622778303, 360582337672944015]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360622306824806375, 360622311508845734⟩, ⟨(-1118826730026468105), (-1118738054064996701)⟩, true⟩

def words08 : List Nat := [360582338076732119, 360582338084432630, 360582339365843057, 360582340647272406, 360582341324750471, 360582342052417011, 360582342052746229, 360582342012443062, 360582342303203330, 360582343731557856]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360523294443792961, 360523299131309788⟩, ⟨1653140091759009094, 1653228865072400786⟩, true⟩

def words09 : List Nat := [360582345736817205, 360582347742003336, 360582348708693856, 360582348709062761, 360582348405339472, 360582347267142105, 360582346263055619, 360582346263424580, 360582345127744995, 360582343019348089]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk279
