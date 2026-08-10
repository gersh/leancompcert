import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942A

def state06 : KState := ⟨⟨360577683343094205, 360577741956131255⟩, ⟨405784741252388963, 409515452052948867⟩, true⟩

def words05 : List Nat := [360582085557108241, 360582085625600492, 360582085806320006, 360582086058293463, 360582086232772496, 360582086407451368, 360582086524816987, 360582086530127086, 360582086531240876, 360582086486706823]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587604740259604, 360587663366169387⟩, ⟨(-529448646082241493), (-525716721831682755)⟩, true⟩

def words06 : List Nat := [360582086508105738, 360582086578493753, 360582086579715616, 360582086579597599, 360582086579259867, 360582086514081821, 360582086585166147, 360582086666379904, 360582086667617466, 360582086712460064]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602234972878729, 360602293611666487⟩, ⟨(-1908731214707146361), (-1904998076386631351)⟩, true⟩

def words07 : List Nat := [360582086841197938, 360582086970333402, 360582087211513111, 360582087340793817, 360582087372752374, 360582087404834821, 360582087489992881, 360582087645186365, 360582087860609542, 360582088076337136]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587733640623267, 360587792292433550⟩, ⟨(-541543004427707591), (-537808638280819295)⟩, true⟩

def words08 : List Nat := [360582088207536348, 360582088349606745, 360582088488817692, 360582088628423412, 360582088729125242, 360582088730490751, 360582088719124822, 360582088641814935, 360582088564249815, 360582088581174991]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557644789582980, 360557703454242711⟩, ⟨2295776150421596506, 2299511728208512140⟩, true⟩

def words09 : List Nat := [360582088755172589, 360582088929437716, 360582089047482087, 360582089053538914, 360582089054681569, 360582089032452386, 360582089009844164, 360582088949785382, 360582088777464387, 360582088520289461]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942B
