import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk764

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585137977742716, 360585175859218858⟩, ⟨(-230703178068449192), (-228748438711461906)⟩, true⟩

def state01 : KState := ⟨⟨360583877755041939, 360583915646893963⟩, ⟨(-134549646536853972), (-132594114411863106)⟩, true⟩

def words00 : List Nat := [360582181809880221, 360582181743319020, 360582181505628486, 360582181439315906, 360582181372733118, 360582181153050606, 360582180981301381, 360582180724030946, 360582180466558749, 360582180371679507]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557603911548068, 360557641813673807⟩, ⟨1873235407242215750, 1875191724434238982⟩, true⟩

def words01 : List Nat := [360582180505721778, 360582180639987776, 360582180688501690, 360582180689596171, 360582180687165694, 360582180546618607, 360582180405761549, 360582180291777199, 360582180104390175, 360582179784420134]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597258966535582, 360597296878943725⟩, ⟨(-1157353938653200226), (-1155396835629445360)⟩, true⟩

def words02 : List Nat := [360582179464211600, 360582179315281487, 360582179387398358, 360582179509576536, 360582179510582583, 360582179510625685, 360582179586745095, 360582179663197416, 360582179818603144, 360582180017518002]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570539297382769, 360570577220183926⟩, ⟨884982244128164347, 886940141540227449⟩, true⟩

def words03 : List Nat := [360582180119526702, 360582180221654361, 360582180284116261, 360582180432608806, 360582180537825264, 360582180643216726, 360582180644199766, 360582180637556387, 360582180459948956, 360582180309424380]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569571083894638, 360569609016951422⟩, ⟨959003037012456767, 960961718415328239⟩, true⟩

def words04 : List Nat := [360582180177586841, 360582180178677121, 360582180100635989, 360582179928572274, 360582179756334480, 360582179541449154, 360582179427644661, 360582179266090362, 360582179104424196, 360582178823601721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603318937791085, 360603356881125618⟩, ⟨(-1621219851383919415), (-1619260384195198451)⟩, true⟩

def words05 : List Nat := [360582178660066484, 360582178626344127, 360582178608839004, 360582178679499674, 360582178680514388, 360582178606945645, 360582178586329987, 360582178726325700, 360582179004190420, 360582179282294905]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599949666913987, 360599987620645886⟩, ⟨(-1363731189349285419), (-1361770927126562053)⟩, true⟩

def words06 : List Nat := [360582179398417515, 360582179399507598, 360582179460081929, 360582179576516490, 360582179610263499, 360582179681756474, 360582179682727999, 360582179652413849, 360582179708756007, 360582179942870958]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565086085335827, 360565124049331173⟩, ⟨1302547825054599080, 1304508872174230762⟩, true⟩

def words07 : List Nat := [360582180347342052, 360582180752018872, 360582181052781931, 360582181183021712, 360582181183954581, 360582181162132985, 360582181221320303, 360582181222410597, 360582181134097564, 360582180912199560]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578023434811444, 360578061409108800⟩, ⟨313081295872145055, 315043130941407161⟩, true⟩

def words08 : List Nat := [360582180690060260, 360582180720805899, 360582180747517149, 360582180774428143, 360582180775433995, 360582180656620234, 360582180408609375, 360582180331586120, 360582180254260605, 360582180158369376]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588819442291189, 360588857426989565⟩, ⟨(-512755261081347249), (-510792630389961857)⟩, true⟩

def words09 : List Nat := [360582180105504908, 360582179967844888, 360582179861864869, 360582180043852170, 360582180182603123, 360582180321547256, 360582180355506335, 360582180356598555, 360582180397880764, 360582180486421600]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk764
