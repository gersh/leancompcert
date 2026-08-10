import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592868719099950, 360592883250162276⟩, ⟨(-499783256800713457), (-499309974249550059)⟩, true⟩

def state01 : KState := ⟨⟨360563242103268725, 360563256640656848⟩, ⟨928337883826746062, 928811471312479322⟩, true⟩

def words00 : List Nat := [360582524338148884, 360582524566378089, 360582524776295672, 360582524986407847, 360582525007943305, 360582525008606801, 360582524599897838, 360582523977034081, 360582523354077522, 360582522591109296]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360508817184897497, 360508831728531919⟩, ⟨3552522277888333433, 3552996166540143877⟩, true⟩

def words01 : List Nat := [360582522192028734, 360582522041424897, 360582521890762434, 360582521417460615, 360582520513876064, 360582519503191350, 360582518492343526, 360582517609006322, 360582516295474810, 360582514768070288]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360539010726165433, 360539025276075393⟩, ⟨2096435546738686160, 2096909738026929478⟩, true⟩

def words02 : List Nat := [360582513240578818, 360582512142026967, 360582511324750052, 360582510457652049, 360582509590534349, 360582508359978849, 360582506699296408, 360582505272836030, 360582503846241753, 360582502566932265]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528301409067576, 360528315965296310⟩, ⟨2612981096345023276, 2613455592419607250⟩, true⟩

def words03 : List Nat := [360582501666091033, 360582500486719640, 360582499307270019, 360582498459537235, 360582497828646965, 360582496913337431, 360582495998002935, 360582494749511968, 360582493198563299, 360582492076250282]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360534520753504299, 360534535315985415⟩, ⟨2312825709273680611, 2313300506994343643⟩, true⟩

def words04 : List Nat := [360582490953757724, 360582490018083834, 360582488652662651, 360582487014326519, 360582485375938488, 360582483630703709, 360582482297175759, 360582481392031221, 360582480486857211, 360582479367943847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482A
