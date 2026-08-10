import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171A

def state06 : KState := ⟨⟨360612171621985056, 360612173307561423⟩, ⟨(-491357770076934306), (-491338189941695266)⟩, true⟩

def words05 : List Nat := [360583528078252537, 360583529339328067, 360583531678914773, 360583535774705566, 360583538323540710, 360583540872114026, 360583540872311273, 360583540591006384, 360583540545659817, 360583542214388433]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360645390713332330, 360645392400951855⟩, ⟨(-1061781643889523568), (-1061762028683234142)⟩, true⟩

def words06 : List Nat := [360583546741782117, 360583547910010518, 360583547910205827, 360583547365484595, 360583546820787843, 360583545638047403, 360583549267108170, 360583552895787914, 360583554192882307, 360583557794424383]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360662232953428595, 360662234643103513⟩, ⟨(-1351524296527475378), (-1351504646020006120)⟩, true⟩

def words07 : List Nat := [360583559430233611, 360583561065913865, 360583563677901120, 360583564414472906, 360583564414673516, 360583562162026625, 360583559998995510, 360583562738283001, 360583567317731807, 360583571896696436]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360692616779255075, 360692618471002297⟩, ⟨(-1874082476055775318), (-1874062789935896418)⟩, true⟩

def words08 : List Nat := [360583574268777701, 360583576702600047, 360583582509248206, 360583588315283896, 360583591792708671, 360583594309096276, 360583594398079970, 360583594487076613, 360583597947777623, 360583604289748392]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360544552938615981, 360544554632416143⟩, ⟨672263630000701366, 672283351420880372⟩, true⟩

def words09 : List Nat := [360583614002273013, 360583623713713001, 360583630825151191, 360583634589758709, 360583636726473856, 360583638862997415, 360583642677297849, 360583643145939975, 360583643146140219, 360583640873777823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171B
