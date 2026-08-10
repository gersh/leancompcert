import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571A

def state06 : KState := ⟨⟨362478855570957845, 362478903291696458⟩, ⟨344715581193026583, 346558195211730315⟩, true⟩

def words05 : List Nat := [371284965153037050, 371284965526355450, 371284965897601462, 371284965990353544, 371284966052499641, 371284966115564323, 371284966433352154, 371284966435279365, 371284966345117701, 371284966241227804]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480670832696956, 362480718570709424⟩, ⟨241037515236810498, 242881116717722906⟩, true⟩

def words06 : List Nat := [371284966232756203, 371284966234916797, 371284966510091318, 371284966802262487, 371284967015323411, 371284967017251129, 371284966857000762, 371284966854070393, 371284966970266020, 371284966972261248]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499216621614234, 362499264377165772⟩, ⟨(-819341052263529399), (-817496447983323915)⟩, true⟩

def words07 : List Nat := [371284966899399501, 371284966761852960, 371284966790162686, 371284966844507373, 371284966989883931, 371284967136045205, 371284967282780546, 371284967284724519, 371284967479942074, 371284967732336488]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484992579346890, 362485040352106996⟩, ⟨(-5923331875502768), (-4077743521753312)⟩, true⟩

def words08 : List Nat := [371284968260639696, 371284968381813207, 371284968439513334, 371284968497863356, 371284968647696082, 371284968649842869, 371284968799777327, 371284968952567899, 371284969048383265, 371284969051665987]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506987076321294, 362507034866520970⟩, ⟨(-1263864707745056329), (-1262018121935839881)⟩, true⟩

def words09 : List Nat := [371284969360262301, 371284969669863553, 371284970284468751, 371284970492092807, 371284970649982208, 371284970808433083, 371284971091517632, 371284971223384119, 371284971610421167, 371284971998355452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571B
