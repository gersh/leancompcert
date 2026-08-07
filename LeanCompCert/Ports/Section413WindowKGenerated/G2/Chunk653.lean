import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588760769102308, 360588788099972084⟩, ⟨(-383462826912828221), (-382257243059462065)⟩, true⟩

def state01 : KState := ⟨⟨360560013942989649, 360560041282629398⟩, ⟨1493678294794357498, 1494884451370591454⟩, true⟩

def words00 : List Nat := [360582934327602069, 360582934300747473, 360582934100789251, 360582933823477788, 360582933545922132, 360582933153202206, 360582932526562347, 360582931720264176, 360582930913813749, 360582930341753125]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537896793167277, 360537924141470073⟩, ⟨2938333340492317796, 2939540062894975904⟩, true⟩

def words01 : List Nat := [360582929992034643, 360582929832309641, 360582929672493654, 360582929346316134, 360582928962914756, 360582928521096041, 360582928079035026, 360582927544535878, 360582926973732928, 360582926285727498]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574110196733334, 360574137553721118⟩, ⟨572736021176849601, 573943310925233699⟩, true⟩

def words02 : List Nat := [360582925597533294, 360582925089400973, 360582924727368204, 360582924599461643, 360582924471476485, 360582924135091732, 360582923628718170, 360582923356531472, 360582923084088226, 360582922848546241]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582221640901981, 360582249006677820⟩, ⟨42697480919074440, 43905344832144494⟩, true⟩

def words03 : List Nat := [360582922714917066, 360582922362577616, 360582922010072805, 360582921831603566, 360582921770097866, 360582921616507692, 360582921462822554, 360582921165015747, 360582920967911856, 360582920958695454]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572785224571002, 360572812599004734⟩, ⟨659282976213833263, 660491405877603223⟩, true⟩

def words04 : List Nat := [360582921025928204, 360582921026849278, 360582920972286342, 360582920767175934, 360582920561935078, 360582920195244454, 360582919945409080, 360582919871405447, 360582919797308332, 360582919583027345]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583806889244278, 360583834272380380⟩, ⟨(-61089063672471488), (-59880065265255030)⟩, true⟩

def words05 : List Nat := [360582919429123452, 360582919198031602, 360582918968271574, 360582918969192749, 360582918837457778, 360582918506829516, 360582918176035074, 360582918098980719, 360582918113755538, 360582918128727969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602210521427949, 360602237913332857⟩, ⟨(-1264162751599262801), (-1262953180020085203)⟩, true⟩

def words06 : List Nat := [360582918129548398, 360582918027249938, 360582917933317476, 360582917979240251, 360582917980013091, 360582917920124439, 360582917920953446, 360582917832250618, 360582917839160039, 360582918135755337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562401168148948, 360562428568740992⟩, ⟨1338467457270391627, 1339677596770721005⟩, true⟩

def words07 : List Nat := [360582918665628035, 360582919195661087, 360582919512170322, 360582919595450671, 360582919615008446, 360582919634818169, 360582919653691970, 360582919654613204, 360582919514355733, 360582919201912769]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587412202026112, 360587439611309398⟩, ⟨(-296817162557554143), (-295606454780007149)⟩, true⟩

def words08 : List Nat := [360582918889254173, 360582918894686206, 360582919164796608, 360582919435081345, 360582919504454154, 360582919505375469, 360582919341422015, 360582919172097306, 360582919002508643, 360582919012835908]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582500967917615, 360582528385975079⟩, ⟨24372980926089783, 25584262488986907⟩, true⟩

def words09 : List Nat := [360582919013656930, 360582918944821310, 360582919039489654, 360582919384842418, 360582919519263100, 360582919653823800, 360582919671221634, 360582919672145170, 360582919587578690, 360582919582649223]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653
