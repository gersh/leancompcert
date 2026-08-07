import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618637910851259, 360618671011431406⟩, ⟨(-2603008202643414513), (-2601407382208592925)⟩, true⟩

def state01 : KState := ⟨⟨360591946164719755, 360591979274993296⟩, ⟨(-691910388406498270), (-690308873880064802)⟩, true⟩

def words00 : List Nat := [360582339399359496, 360582339590686896, 360582339735788627, 360582339881189744, 360582339976815013, 360582339977830833, 360582339878911506, 360582339682690980, 360582339486281619, 360582339570564088]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550869948735842, 360550903068561774⟩, ⟨2249843708850345687, 2251445907473691637⟩, true⟩

def words01 : List Nat := [360582339792237955, 360582340014098384, 360582340130165777, 360582340131181944, 360582340116128723, 360582340051915600, 360582339987424542, 360582339841376022, 360582339500683794, 360582339062801843]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574129411984692, 360574162541406252⟩, ⟨583808745487245659, 585411631394626721⟩, true⟩

def words02 : List Nat := [360582338624709774, 360582338122098958, 360582337745850947, 360582337509438322, 360582337272936901, 360582336870532617, 360582336341827255, 360582335930222547, 360582335518330935, 360582335257187275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591558440590266, 360591591579709762⟩, ⟨(-664778652065485069), (-663175071447804203)⟩, true⟩

def words03 : List Nat := [360582335144023367, 360582334879042619, 360582334613867303, 360582334570123440, 360582334570974058, 360582334549199902, 360582334527315645, 360582334408291383, 360582334528407840, 360582334658792302]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580953541753010, 360580986690439446⟩, ⟨94966717213147451, 96570983254663049⟩, true⟩

def words04 : List Nat := [360582334906713682, 360582335001007625, 360582335001923760, 360582334931652557, 360582334861233852, 360582334619593442, 360582334525258291, 360582334575921151, 360582334576837441, 360582334505976846]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600229472158767, 360600262630458503⟩, ⟨(-1286211425237228118), (-1284606470355129828)⟩, true⟩

def words05 : List Nat := [360582334623336645, 360582334759821177, 360582335040859661, 360582335293681819, 360582335362424040, 360582335431245870, 360582335651389083, 360582335969386286, 360582336220386248, 360582336471594475]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587852473231819, 360587885641210860⟩, ⟨(-399295503054269573), (-397689854504430571)⟩, true⟩

def words06 : List Nat := [360582336625511707, 360582336626528526, 360582336739206274, 360582336893424931, 360582336921012217, 360582336953857942, 360582336954772583, 360582336889967631, 360582336824970218, 360582336815960698]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560588966140529, 360560622143709823⟩, ⟨1554882896639766889, 1556489232571579975⟩, true⟩

def words07 : List Nat := [360582337088522027, 360582337361273958, 360582337482603348, 360582337483620369, 360582337410680190, 360582337243324616, 360582337075657342, 360582337065024587, 360582336860095318, 360582336558226726]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566531185453476, 360566564372620863⟩, ⟨1128978807097719415, 1130585831067659475⟩, true⟩

def words08 : List Nat := [360582336256118219, 360582336080165122, 360582336116894269, 360582336206533501, 360582336207481627, 360582336119505206, 360582335889112571, 360582335522106708, 360582335154813938, 360582334854292891]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579993869353517, 360580027066207243⟩, ⟨163738899171806426, 165346617603475704⟩, true⟩

def words09 : List Nat := [360582334635222054, 360582334293189122, 360582333950971044, 360582333807939445, 360582333808794994, 360582333708988190, 360582333609073400, 360582333412223306, 360582333186715360, 360582333155713568]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716
