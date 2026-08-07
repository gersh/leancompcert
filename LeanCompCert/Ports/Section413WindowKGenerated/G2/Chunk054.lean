import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk054

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360383834317623643, 360383834466512664⟩, ⟨1061824783593525841, 1061825329373799165⟩, true⟩

def state01 : KState := ⟨⟨360400543743630015, 360400543893098404⟩, ⟨970823303365393221, 970823852277204111⟩, true⟩

def words00 : List Nat := [360580432379796333, 360580400451468408, 360580354784565520, 360580292023516735, 360580229285680537, 360580145446337159, 360580086666154361, 360580061664461131, 360580036672006012, 360579993773371455]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360757278388377358, 360757278538427954⟩, ⟨(-962291204618867332), (-962290652554429264)⟩, true⟩

def words01 : List Nat := [360579960609519076, 360579926059715647, 360579891522659654, 360579890681924139, 360579856260353756, 360579793683438559, 360579731129615726, 360579702245316250, 360579734137524003, 360579766888814520]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360185620061064570, 360185620211702655⟩, ⟨2136961189694552889, 2136961744946106737⟩, true⟩

def words02 : List Nat := [360579777691163770, 360579777691225423, 360579754982350811, 360579713979507712, 360579672991765833, 360579606955619303, 360579507460912831, 360579387916171356, 360579268415457586, 360579167494381497]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360172664701861665, 360172664853083099⟩, ⟨2208829456032424862, 2208830014454522328⟩, true⟩

def words03 : List Nat := [360579095031297309, 360579056100065602, 360579017183157679, 360578961287970359, 360578924264937742, 360578878422099678, 360578832596106621, 360578820210996518, 360578774434643328, 360578699782210769]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360740949937637125, 360740950089442517⟩, ⟨(-885204863334830925), (-885204301733015623)⟩, true⟩

def words04 : List Nat := [360578625157205108, 360578583946957329, 360578569724432658, 360578579301653232, 360578579301711138, 360578555683995720, 360578534055145350, 360578520691578476, 360578527281721042, 360578557078667794]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360363874147224759, 360363874299622133⟩, ⟨1171569843056439901, 1171570407887389451⟩, true⟩

def words05 : List Nat := [360578564345102593, 360578571608878973, 360578571608930270, 360578569388790556, 360578569388842609, 360578569065773344, 360578568742815570, 360578544405392828, 360578486940672626, 360578447634400044]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360077103612674810, 360077103765656991⟩, ⟨2738650209907935938, 2738650777935006404⟩, true⟩

def words06 : List Nat := [360578408342501289, 360578386329954348, 360578331213226176, 360578258713771966, 360578186240840092, 360578105145850854, 360578041267318565, 360577956819259204, 360577872402075649, 360577771183926645]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360763962886898639, 360763963040469131⟩, ⟨(-1022478253854488265), (-1022477682606424349)⟩, true⟩

def words07 : List Nat := [360577679671014632, 360577621222815249, 360577562795956338, 360577512720332709, 360577483541027618, 360577426139971358, 360577368759864167, 360577345467328671, 360577379521680932, 360577413563620669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590716467209117, 360590716621374822⟩, ⟨(-73641669620150905), (-73641095107414085)⟩, true⟩

def words08 : List Nat := [360577419521782248, 360577419521844575, 360577398570156802, 360577404553088879, 360577404553141203, 360577402014737485, 360577392134757581, 360577361009431211, 360577329895433404, 360577305385696911]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360055277068429546, 360055277223183961⟩, ⟨2869178733912077070, 2869179311659817084⟩, true⟩

def words09 : List Nat := [360577305602450606, 360577305819136893, 360577305819192619, 360577289340363362, 360577260337635882, 360577207185664651, 360577154053014167, 360577113886843032, 360577041055026438, 360576946188940292]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk054
