import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632A

def state06 : KState := ⟨⟨360592777962228037, 360592803547030615⟩, ⟨(-639594370215507144), (-638501033635288434)⟩, true⟩

def words05 : List Nat := [360582709076166862, 360582709354271278, 360582709789536955, 360582709975988283, 360582709976807925, 360582709951642919, 360582709933866091, 360582710103597970, 360582710263884289, 360582710424354159]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593775073667990, 360593800666937750⟩, ⟨(-702847324214305954), (-701753451959425932)⟩, true⟩

def words06 : List Nat := [360582710425159733, 360582710383252357, 360582710172920578, 360582710109712254, 360582710046270514, 360582709920085660, 360582709800136229, 360582709554605033, 360582709308911439, 360582709433166205]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568291304694456, 360568316906350253⟩, ⟨909633377254183554, 910727780135387788⟩, true⟩

def words07 : List Nat := [360582709594657239, 360582709756315403, 360582709757122448, 360582709709266609, 360582709579130887, 360582709384269961, 360582709242735401, 360582709243625344, 360582709164775385, 360582708938274011]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575986055348807, 360576011665392398⟩, ⟨422733087560438533, 423828021264043939⟩, true⟩

def words08 : List Nat := [360582708733524538, 360582708894656776, 360582709085342433, 360582709276191674, 360582709277011662, 360582709256508136, 360582708987149822, 360582708711750200, 360582708436090057, 360582708268667229]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577750852128877, 360577776470641695⟩, ⟨311029347481027363, 312124817242655657⟩, true⟩

def words09 : List Nat := [360582708163655197, 360582707879841951, 360582707595867452, 360582707659498378, 360582707745967151, 360582707832579907, 360582707833383414, 360582707755730712, 360582707429313507, 360582707352430679]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632B
