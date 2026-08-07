import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk251

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495287368347658, 362495295968375881⟩, ⟨(-238393041608182879), (-238247098344871973)⟩, true⟩

def state01 : KState := ⟨⟨362456575339411886, 362456583946608160⟩, ⟨733534759774425568, 733680882992247410⟩, true⟩

def words00 : List Nat := [371285804821129750, 371285804821941289, 371285804939783877, 371285805520408968, 371285806582072653, 371285806582865324, 371285805532390723, 371285804476023451, 371285803419437315, 371285802619765956]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362457536748378810, 362457545362724918⟩, ⟨709532530041014663, 709678832826992137⟩, true⟩

def words01 : List Nat := [371285801877137988, 371285802298385597, 371285802423627811, 371285802424421358, 371285800853473742, 371285799764605236, 371285799169079313, 371285799169874141, 371285798032424333, 371285796908617713]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488086636788181, 362488095258245788⟩, ⟨(-57972170803813927), (-57825689340602963)⟩, true⟩

def words02 : List Nat := [371285796243044716, 371285796243918696, 371285796079432101, 371285796133502256, 371285796134117518, 371285795868152340, 371285794002700014, 371285793720351901, 371285794195359431, 371285794287757523]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469125638270655, 362469134266942407⟩, ⟨418713979337259119, 418860642129157553⟩, true⟩

def words03 : List Nat := [371285794373172440, 371285794458840493, 371285795725551303, 371285796281353329, 371285796909882684, 371285797538671411, 371285797848527623, 371285797849321590, 371285796052123417, 371285795390336567]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465300019067435, 362465308654814745⟩, ⟨514976894239394528, 515123734947490770⟩, true⟩

def words04 : List Nat := [371285795365508452, 371285795366306307, 371285794503408494, 371285793342113171, 371285792180585686, 371285791367108210, 371285790286075322, 371285790535993311, 371285790711047356, 371285790711870312]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507588428266833, 362507597071213246⟩, ⟨(-548836462294502757), (-548689440493716779)⟩, true⟩

def words05 : List Nat := [371285789898055712, 371285789735572579, 371285790988251158, 371285790989045518, 371285790300786342, 371285789517271173, 371285788750321741, 371285788751211843, 371285789063932509, 371285789931572782]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482732400997658, 362482741051111183⟩, ⟨76562336952664355, 76709539114854333⟩, true⟩

def words06 : List Nat := [371285790792470665, 371285790793266440, 371285790709496849, 371285791457000383, 371285792277104767, 371285792277899534, 371285790995708119, 371285789707759209, 371285788707698865, 371285788708604821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362444070261663899, 362444078918934010⟩, ⟨1050158142597451227, 1050305524927929409⟩, true⟩

def words07 : List Nat := [371285790043575535, 371285791499839784, 371285792970321649, 371285792971117076, 371285792642948624, 371285792635385361, 371285793598186403, 371285793598981563, 371285792470013890, 371285790814284603]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362506204671418389, 362506213335807204⟩, ⟨(-514704661879211992), (-514557100262859264)⟩, true⟩

def words08 : List Nat := [371285789158344504, 371285788431771085, 371285786970309224, 371285787027740226, 371285787028357123, 371285786762004553, 371285785217226030, 371285785052678110, 371285786296460631, 371285787108175794]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502475780194184, 362502484451861831⟩, ⟨(-420737036073863443), (-420589291069606345)⟩, true⟩

def words09 : List Nat := [371285787916384092, 371285788724797047, 371285789914085820, 371285790740919213, 371285792047034464, 371285793353342557, 371285794439251834, 371285794440048237, 371285794399605795, 371285795062906250]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk251
