import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583862279747083, 360583877638514555⟩, ⟨(-100207600813891543), (-99693882343494037)⟩, true⟩

def state01 : KState := ⟨⟨360586825984860961, 360586841350049492⟩, ⟨(-246962854330352835), (-246448817984478833)⟩, true⟩

def words00 : List Nat := [360581863972787847, 360581864008162391, 360581864008770845, 360581863784349358, 360581863559808695, 360581863234435420, 360581863392574234, 360581863594698767, 360581863595312413, 360581863692195996]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594804309833824, 360594819681474852⟩, ⟨(-642128695519114673), (-641614339678237929)⟩, true⟩

def words01 : List Nat := [360581863692761184, 360581863579187958, 360581863636978719, 360581863637662863, 360581863634962466, 360581863280938490, 360581862926800668, 360581862747731328, 360581863009934592, 360581863272281213]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591715907275807, 360591731285414469⟩, ⟨(-489329537759184949), (-488814860123126507)⟩, true⟩

def words02 : List Nat := [360581863272891001, 360581863246960316, 360581863484045651, 360581863806320167, 360581863856028667, 360581863856711517, 360581863499669488, 360581862937279524, 360581862374781182, 360581862418237891]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576616064546431, 360576631449124413⟩, ⟨258683422020245544, 259198418628231354⟩, true⟩

def words03 : List Nat := [360581863024467639, 360581863630816301, 360581863897478863, 360581863898161876, 360581863758108509, 360581863517415700, 360581863441421251, 360581863657141069, 360581863657760118, 360581863552851265]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360631664336949319, 360631679727972223⟩, ⟨(-2468734433194558298), (-2468219117272940730)⟩, true⟩

def words04 : List Nat := [360581863664084852, 360581864144968895, 360581864569537632, 360581864994221809, 360581865066638158, 360581865151539331, 360581865642474445, 360581866133590088, 360581867030649305, 360581868036638589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360608992073813972, 360609007471352838⟩, ⟨(-1345263652507484583), (-1344748013688652713)⟩, true⟩

def words05 : List Nat := [360581868829903948, 360581869623213448, 360581870407844272, 360581871395266522, 360581872012282640, 360581872629383151, 360581873043140245, 360581873185343151, 360581873733399350, 360581874281673682]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578062606941295, 360578078010910750⟩, ⟨187748589189661788, 188264546741389462⟩, true⟩

def words06 : List Nat := [360581875051269831, 360581875414736914, 360581875573194493, 360581875731714771, 360581875732287495, 360581875908360184, 360581876026169778, 360581876144095944, 360581876144708376, 360581875964244246]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611461413439157, 360611476823858969⟩, ⟨(-1468020394385121663), (-1467504117057679843)⟩, true⟩

def words07 : List Nat := [360581875987704930, 360581876087987030, 360581876486086603, 360581876896494291, 360581876968447227, 360581877040449975, 360581877174584705, 360581877514078968, 360581878111632905, 360581878709317962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591020466673211, 360591035883621604⟩, ⟨(-454574369454536668), (-454057768409186356)⟩, true⟩

def words08 : List Nat := [360581878992097148, 360581879157606160, 360581879650195679, 360581880142965805, 360581880462037256, 360581880462721073, 360581880376036748, 360581880086569940, 360581879796967683, 360581879831749104]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546741042214861, 360546756465598077⟩, ⟨1741567278098383343, 1742084198279494015⟩, true⟩

def words09 : List Nat := [360581880318992681, 360581880806347598, 360581881048405458, 360581881049089435, 360581880989354434, 360581880600432362, 360581880226957620, 360581880227641680, 360581879838309121, 360581879130885971]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk495
