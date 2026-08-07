import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479932671889965, 362479980288505405⟩, ⟨282633611699309680, 284470277155611152⟩, true⟩

def state01 : KState := ⟨⟨362484887725633915, 362484935359476255⟩, ⟨(-299249565287463), 1538399636136841⟩, true⟩

def words00 : List Nat := [371284962175168930, 371284962177292182, 371284962116790874, 371284962183500208, 371284962199113191, 371284962201072258, 371284962029837862, 371284962099323618, 371284962294965717, 371284962296958940]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482365119681028, 362482412771120408⟩, ⟨143780936594601051, 145619590844545757⟩, true⟩

def words01 : List Nat := [371284962297927073, 371284962298218761, 371284962376003521, 371284962378150051, 371284962404669954, 371284962465514224, 371284962524121116, 371284962526047092, 371284962175875648, 371284962133705222]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473389038333243, 362473436706899688⟩, ⟨656584066071355115, 658423698709907195⟩, true⟩

def words02 : List Nat := [371284962334764052, 371284962336699262, 371284962288007203, 371284962173913900, 371284962059106724, 371284962037856798, 371284961863418130, 371284961815240313, 371284961766396578, 371284961714753879]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510388967335021, 362510436653303203⟩, ⟨(-1457396345605767643), (-1455555718718743111)⟩, true⟩

def words03 : List Nat := [371284961619322219, 371284961726619725, 371284961993799777, 371284962106067349, 371284962194923061, 371284962284392880, 371284962563963865, 371284962705281803, 371284963152405301, 371284963600351405]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491449521071578, 362491497224452570⟩, ⟨(-375177325052404437), (-373335703108770157)⟩, true⟩

def words04 : List Nat := [371284963983805237, 371284963985731921, 371284964240917694, 371284964523463072, 371284964820329996, 371284964822256770, 371284964710921031, 371284964594071856, 371284964663997199, 371284964780521427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571
