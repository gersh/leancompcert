import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604A

def state06 : KState := ⟨⟨360580528569561078, 360580551855791975⟩, ⟨107000772306663263, 107951892994146137⟩, true⟩

def words05 : List Nat := [360582336841087967, 360582337160508136, 360582337340777995, 360582337341624128, 360582337312240122, 360582337188433170, 360582337213283921, 360582337392993797, 360582337393760507, 360582337365103820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597970344255709, 360597993638471861⟩, ⟨(-947568290944159105), (-946616687428009613)⟩, true⟩

def words06 : List Nat := [360582337510065954, 360582337824091842, 360582338218119578, 360582338612293285, 360582338764512926, 360582338930808875, 360582339029347143, 360582339128124943, 360582339318306400, 360582339578055662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584569654057179, 360584592956353888⟩, ⟨(-137222224852753128), (-136270132665123706)⟩, true⟩

def words07 : List Nat := [360582339700896102, 360582339823818037, 360582339873972477, 360582340060850529, 360582340081736204, 360582340102762181, 360582340103517744, 360582339959938183, 360582339811633898, 360582339849879704]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572127913600318, 360572151223863661⟩, ⟨615288007131346516, 616240581181381918⟩, true⟩

def words08 : List Nat := [360582340050914634, 360582340051761239, 360582339980386281, 360582339771630228, 360582339562742873, 360582339284008543, 360582339202147880, 360582339112339411, 360582339022457377, 360582338702474694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630036762527386, 360630060080779121⟩, ⟨(-2887922326053495192), (-2886969268746880298)⟩, true⟩

def words09 : List Nat := [360582338584400314, 360582338634986025, 360582338958598101, 360582339387507657, 360582339566786293, 360582339746126591, 360582340198540896, 360582340790152525, 360582341579585703, 360582342369191761]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604B
