import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk530

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596905865622714, 360596923571448508⟩, ⟨(-793513711743391267), (-792879656172709147)⟩, true⟩

def state01 : KState := ⟨⟨360575629782425399, 360575647495255710⟩, ⟨334121354379415871, 334755781222904475⟩, true⟩

def words00 : List Nat := [360581963910972373, 360581963911707176, 360581963657555732, 360581963708624928, 360581963709239874, 360581963670868996, 360581963515060739, 360581963181121670, 360581962847058679, 360581962450570234]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555922531084033, 360555940250843182⟩, ⟨1378875715386073555, 1379510509562241979⟩, true⟩

def words01 : List Nat := [360581962332049367, 360581962204929684, 360581962077734217, 360581961724762479, 360581961269798861, 360581960624923140, 360581959979856039, 360581959690021448, 360581959422629822, 360581958932653108]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563861549866771, 360563879276558715⟩, ⟨957942603726968230, 958577765514685148⟩, true⟩

def words02 : List Nat := [360581958442523643, 360581958153382624, 360581958050716218, 360581958059246685, 360581958059937027, 360581957720324951, 360581957025847987, 360581956437547541, 360581955849046807, 360581955417714942]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549560960216067, 360549578693917264⟩, ⟨1716408054949289134, 1717043588472512410⟩, true⟩

def words03 : List Nat := [360581955077514343, 360581954468528426, 360581953859412026, 360581953545246186, 360581953409621440, 360581953184872625, 360581952960058275, 360581952521272913, 360581951920103194, 360581951310592840]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559896964518931, 360559914705142477⟩, ⟨1168067865950106350, 1168703766669736528⟩, true⟩

def words04 : List Nat := [360581950700856501, 360581950092889865, 360581949430484313, 360581948590269620, 360581947749966653, 360581946786973550, 360581946102719497, 360581945773224488, 360581945443660091, 360581944936370936]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568035437525604, 360568053185099032⟩, ⟨736211156129594082, 736847425574615492⟩, true⟩

def words05 : List Nat := [360581944521700398, 360581944461801863, 360581944401707477, 360581944052746553, 360581943498498693, 360581942631957925, 360581941765310640, 360581941017875802, 360581940506467302, 360581940245513179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569805327462053, 360569823082039765⟩, ⟨642107375060499418, 642744016186406890⟩, true⟩

def words06 : List Nat := [360581939984450623, 360581939496930247, 360581938790949198, 360581938328496331, 360581937865853032, 360581937314295890, 360581936692929588, 360581935787722771, 360581934882409249, 360581934331638153]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558774038039547, 360558791799542719⟩, ⟨1227705387095822864, 1228342395790975784⟩, true⟩

def words07 : List Nat := [360581934136829758, 360581934170369978, 360581934171031478, 360581934055721344, 360581934056341955, 360581933847781537, 360581933783814795, 360581933784550598, 360581933576052530, 360581933140834938]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360615180421222193, 360615198189679298⟩, ⟨(-1766712669577864389), (-1766075291733581107)⟩, true⟩

def words08 : List Nat := [360581932705477408, 360581932261931097, 360581932024996642, 360581932050321475, 360581932050999986, 360581931773611077, 360581931783628896, 360581931966176341, 360581932502503257, 360581933129843666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593954403104841, 360593972178574605⟩, ⟨(-639695573106182858), (-639057822925881958)⟩, true⟩

def words09 : List Nat := [360581933499024253, 360581933868266955, 360581934591327562, 360581935492738921, 360581936060071582, 360581936627491740, 360581936926930415, 360581936963229618, 360581937190477207, 360581937417968856]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk530
