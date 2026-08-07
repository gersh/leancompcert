import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk051

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360621311541952764, 360621311673932757⟩, ⟨(-242322389084497028), (-242321932104257088)⟩, true⟩

def state01 : KState := ⟨⟨360773366878103059, 360773367010626850⟩, ⟨(-1019397902663277207), (-1019397442906954445)⟩, true⟩

def words00 : List Nat := [360573854215277369, 360573863817392061, 360573863817444824, 360573843900382304, 360573823991113097, 360573793981808829, 360573828969738194, 360573865416353686, 360573876317238048, 360573915348935018]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360849216152010624, 360849216285079999⟩, ⟨(-1407741395504461452), (-1407740932957409152)⟩, true⟩

def words01 : List Nat := [360573968370557404, 360574021371456930, 360574112207002435, 360574165401015891, 360574183215158963, 360574201022343514, 360574201022391422, 360574213172459453, 360574266884051900, 360574320574680193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360841566189467530, 360841566323089549⟩, ⟨(-1369739621442054561), (-1369739156062784143)⟩, true⟩

def words02 : List Nat := [360574354164236098, 360574378693856690, 360574425082607168, 360574471453272403, 360574500619553915, 360574526413460983, 360574533197146527, 360574539978193119, 360574560639579902, 360574612677394211]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360468386579368164, 360468386713538139⟩, ⟨546501408878211368, 546501877071281560⟩, true⟩

def words03 : List Nat := [360574662939319908, 360574713181671927, 360574736779566803, 360574751565527440, 360574751565576418, 360574743221685035, 360574734881025863, 360574731606046518, 360574730725361918, 360574710035925548]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360817028009922971, 360817028144642620⟩, ⟨(-1247305951475560743), (-1247305480454456275)⟩, true⟩

def words04 : List Nat := [360574689354525147, 360574705371395638, 360574741010421296, 360574776635604050, 360574776635658617, 360574776523591541, 360574779013847958, 360574798913564457, 360574832905659167, 360574879924791241]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360497411345103065, 360497411480378573⟩, ⟨401475255612382431, 401475729498984815⟩, true⟩

def words05 : List Nat := [360574898550940828, 360574917169868375, 360574973023543320, 360575048018056620, 360575113130215541, 360575178217131918, 360575223483221337, 360575231935681304, 360575231935729791, 360575216854312485]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360726133673738653, 360726133809565128⟩, ⟨(-780962608276948224), (-780962131544582576)⟩, true⟩

def words06 : List Nat := [360575201778720924, 360575196132799564, 360575176054885990, 360575137218914188, 360575098397971148, 360575049860111071, 360575054422499339, 360575075207817888, 360575077304369919, 360575106516673119]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361066064908441562, 361066065044821342⟩, ⟨(-2540659677088825644), (-2540659197493098422)⟩, true⟩

def words07 : List Nat := [360575172682037719, 360575238821838062, 360575303240330227, 360575358276162544, 360575378461903984, 360575398639851184, 360575437702919546, 360575495591633767, 360575590296208978, 360575684964239776]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360706798822319259, 360706798959258313⟩, ⟨(-679921907724136179), (-679921425228520383)⟩, true⟩

def words08 : List Nat := [360575749796826794, 360575778173633047, 360575826768598132, 360575875344836202, 360575898877861433, 360575898877920170, 360575885998604847, 360575842714030102, 360575799446127555, 360575818141452781]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360701357930759423, 360701358068253324⟩, ⟨(-651252728191547961), (-651252242813428121)⟩, true⟩

def words09 : List Nat := [360575860344290199, 360575902530885293, 360575925304216588, 360575954702073918, 360575974478640691, 360575994247611993, 360576050594116311, 360576093162808961, 360576117252266435, 360576141332469162]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk051
