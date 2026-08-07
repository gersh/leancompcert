import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk570

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

def state06 : KState := ⟨⟨360605637847369486, 360605658492651735⟩, ⟨(-1356763269149675963), (-1355967376755809349)⟩, true⟩

def words05 : List Nat := [360581891162438903, 360581891429950532, 360581891900247423, 360581892574878641, 360581893170985281, 360581893767200821, 360581894077652090, 360581894187885068, 360581894605007349, 360581895022387355]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605182794479782, 360605203447250787⟩, ⟨(-1330846293213538768), (-1330049973473778832)⟩, true⟩

def words06 : List Nat := [360581895636124266, 360581896025574895, 360581896217728865, 360581896409975725, 360581896479413247, 360581896702055688, 360581897160474383, 360581897619034711, 360581897857261521, 360581898266450140]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619886339701805, 360619906999991525⟩, ⟨(-2170139635504207617), (-2169342886634697853)⟩, true⟩

def words07 : List Nat := [360581898595909067, 360581898925579306, 360581899561913819, 360581899892598116, 360581899961331888, 360581900030126128, 360581900405641960, 360581901026330342, 360581901692814916, 360581902359452034]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614607811910623, 360614628479773516⟩, ⟨(-1869040236377715130), (-1868243055194539260)⟩, true⟩

def words08 : List Nat := [360581902848623900, 360581903032149211, 360581903305836188, 360581903579744177, 360581903633224849, 360581903751841421, 360581903752556929, 360581903718173397, 360581903955209689, 360581904529322578]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576523988679231, 360576544664042709⟩, ⟨305430947648434761, 306228557078063743⟩, true⟩

def words09 : List Nat := [360581905278454620, 360581906027726352, 360581906622314856, 360581906911353393, 360581907051120007, 360581907191103741, 360581907637499271, 360581907778436914, 360581907779158266, 360581907686058087]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk570
