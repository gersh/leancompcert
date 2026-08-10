import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638A

def state06 : KState := ⟨⟨362518263141903499, 362518323230510697⟩, ⟨(-2102286529997481760), (-2099694713751898940)⟩, true⟩

def words05 : List Nat := [371285440934125471, 371285441160234301, 371285441630772630, 371285441898704871, 371285442089974916, 371285442281925088, 371285442718472501, 371285443057589857, 371285443573944815, 371285444091227694]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503924999012866, 362503985107231056⟩, ⟨(-1186607328401152505), (-1184014259695023743)⟩, true⟩

def words06 : List Nat := [371285444560999727, 371285444747243253, 371285445178268105, 371285445610448165, 371285446099186555, 371285446369108313, 371285446620066379, 371285446871770226, 371285447226882300, 371285447519598249]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489997164848964, 362490057292613069⟩, ⟨(-296918550654221052), (-294324233449302396)⟩, true⟩

def words07 : List Nat := [371285447987674156, 371285448456647745, 371285448906510427, 371285449063917020, 371285449231305064, 371285449399709005, 371285449692038564, 371285449761276327, 371285449835027892, 371285449909612658]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503800416866409, 362503860564112449⟩, ⟨(-1178651337447367698), (-1176055775639929378)⟩, true⟩

def words08 : List Nat := [371285450202952556, 371285450431201351, 371285450883166606, 371285451335981410, 371285451751155695, 371285451916223152, 371285452260957180, 371285452606851600, 371285453052463095, 371285453342819311]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499081361276012, 362499141528301496⟩, ⟨(-877070697120610352), (-874473871506872588)⟩, true⟩

def words09 : List Nat := [371285453624290750, 371285453906450342, 371285454410592407, 371285454814139606, 371285455262785360, 371285455712302910, 371285456134317422, 371285456272843275, 371285456488494538, 371285456705348697]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638B
