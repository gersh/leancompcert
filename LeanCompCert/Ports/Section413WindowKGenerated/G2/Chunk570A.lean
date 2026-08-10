import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk570A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618296070894933, 360618316671039834⟩, ⟨(-2077640757315718977), (-2076847439105632489)⟩, true⟩

def state01 : KState := ⟨⟨360607399278176572, 360607419885810279⟩, ⟨(-1456543829760601985), (-1455750084649820045)⟩, true⟩

def words00 : List Nat := [360581881901083731, 360581882367541357, 360581882678966936, 360581882990468357, 360581883131676783, 360581883429985963, 360581883974357540, 360581884518875941, 360581884889642466, 360581885338360668]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611625168854363, 360611645783987108⟩, ⟨(-1697521034403452785), (-1696726861736081281)⟩, true⟩

def words01 : List Nat := [360581885993080785, 360581886648010793, 360581887256004929, 360581887702589799, 360581887864409385, 360581888026265661, 360581888175971430, 360581888563668612, 360581889086185759, 360581889608863276]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599420712990988, 360599441335696772⟩, ⟨(-1001611442962981088), (-1000816838442419614)⟩, true⟩

def words02 : List Nat := [360581889956547416, 360581890311760200, 360581890906616405, 360581891501699829, 360581892017166840, 360581892226460120, 360581892280828373, 360581892335281724, 360581892380933855, 360581892689549196]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558979226497940, 360558999856689086⟩, ⟨1304942508418345953, 1305737539865976631⟩, true⟩

def words03 : List Nat := [360581892973572820, 360581893257735440, 360581893388532517, 360581893389327372, 360581893213843078, 360581892745210646, 360581892276346024, 360581892114918941, 360581891869046099, 360581891468538069]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605954956703001, 360605975594407573⟩, ⟨(-1374851645974253889), (-1374056185923368903)⟩, true⟩

def words04 : List Nat := [360581891067862216, 360581891037093375, 360581891037747836, 360581891003722367, 360581890969632389, 360581890675730116, 360581890337016708, 360581890305737023, 360581890471993176, 360581890894999616]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk570A
