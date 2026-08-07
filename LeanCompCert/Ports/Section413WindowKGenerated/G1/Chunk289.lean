import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk289

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362456203899200943, 362456215435921207⟩, ⟨840216425055251455, 840441801348794119⟩, true⟩

def state01 : KState := ⟨⟨362488789446999416, 362488800991986848⟩, ⟨(-101639270183050588), (-101413654926098032)⟩, true⟩

def words00 : List Nat := [371285295652476560, 371285295653493170, 371285295337393361, 371285295429355710, 371285295430071000, 371285295247516015, 371285293625406064, 371285293045887393, 371285293081816193, 371285293204123195]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477424763940730, 362477436317346048⟩, ⟨227053678296542721, 227279536956867899⟩, true⟩

def words01 : List Nat := [371285293218772935, 371285293233747885, 371285294124103348, 371285294495537706, 371285295226383085, 371285295957522013, 371285296338305730, 371285296339231258, 371285295493101735, 371285295222496701]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475353758261565, 362475365319896569⟩, ⟨286972069477047702, 287198166182848064⟩, true⟩

def words02 : List Nat := [371285295875122733, 371285295876046356, 371285295208316080, 371285294556806063, 371285293904983756, 371285293412269300, 371285292440873862, 371285292553429809, 371285292666538205, 371285292667500539]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362539186627376911, 362539198197360380⟩, ⟨(-1560069847794498857), (-1559843509524455595)⟩, true⟩

def words03 : List Nat := [371285292479855262, 371285292635794033, 371285293985711498, 371285294468408217, 371285294769632603, 371285295071124412, 371285296240511493, 371285297110333197, 371285298973473033, 371285300836884776]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513333070762120, 362513344649081169⟩, ⟨(-811871552020999459), (-811644972477323699)⟩, true⟩

def words04 : List Nat := [371285302468559020, 371285302823133614, 371285304217162234, 371285305611595537, 371285307055683301, 371285307130887493, 371285307206895209, 371285307283200313, 371285308552258233, 371285309521711568]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471256779675000, 362471268366345554⟩, ⟨406571862474112128, 406798683835366998⟩, true⟩

def words05 : List Nat := [371285310947347310, 371285312373287419, 371285313788114541, 371285313877005266, 371285314324687718, 371285314772787145, 371285316063094863, 371285316064019947, 371285315766234480, 371285315282223848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362508097089291151, 362508108684240706⟩, ⟨(-660420060765314411), (-660192999601459187)⟩, true⟩

def words06 : List Nat := [371285315504969039, 371285315624746092, 371285316344044266, 371285317063659912, 371285317591788519, 371285317592729714, 371285317709077720, 371285318288028772, 371285319832761888, 371285320620328468]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499407798290432, 362499419401687329⟩, ⟨(-408653840992082649), (-408426535067142045)⟩, true⟩

def words07 : List Nat := [371285321212380574, 371285321804686746, 371285322893087769, 371285323567023854, 371285324454053923, 371285325341385809, 371285326223691185, 371285326224616850, 371285326007316359, 371285326494780489]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458266638055096, 362458278249687926⟩, ⟨783907108701494490, 784134653347467108⟩, true⟩

def words08 : List Nat := [371285328017917837, 371285328163602166, 371285328310079801, 371285328456866867, 371285328473248014, 371285328474267892, 371285327895344512, 371285327501129038, 371285327106644208, 371285326702718194]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362533173745137190, 362533185365154555⟩, ⟨(-1387996699904857683), (-1387768912150109763)⟩, true⟩

def words09 : List Nat := [371285325823205552, 371285325877175494, 371285326969430968, 371285327346176408, 371285327532607232, 371285327719310981, 371285328951031783, 371285329612857337, 371285331263685256, 371285332914820080]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk289
