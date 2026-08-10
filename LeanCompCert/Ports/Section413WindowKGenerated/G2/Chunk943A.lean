import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557644789582980, 360557703454242711⟩, ⟨2295776150421596506, 2299511728208512140⟩, true⟩

def state01 : KState := ⟨⟨360582571110618703, 360582629788164565⟩, ⟨(-54911603752421591), (-51174810739418721)⟩, true⟩

def words00 : List Nat := [360582088262805715, 360582088099695639, 360582088010431314, 360582087938419504, 360582087866279086, 360582087698854103, 360582087452788481, 360582087319495930, 360582087185803597, 360582087170540541]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585844077671679, 360585902768258683⟩, ⟨(-363638355115365362), (-359900332129121508)⟩, true⟩

def words01 : List Nat := [360582087171791180, 360582087092593017, 360582087013135206, 360582087071228835, 360582087082041157, 360582087093077714, 360582087094294475, 360582087040518047, 360582087029491794, 360582087071519579]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581743348702581, 360581802052142124⟩, ⟨23145128124556199, 26884363427131653⟩, true⟩

def words02 : List Nat := [360582087225413075, 360582087267509055, 360582087268727614, 360582087238704351, 360582087208488277, 360582087076261685, 360582087043430369, 360582087083997877, 360582087085226563, 360582087055464791]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585983067448374, 360586041783801232⟩, ⟨(-376802238149544156), (-373061784669705530)⟩, true⟩

def words03 : List Nat := [360582087162844513, 360582087273670834, 360582087381982776, 360582087406436463, 360582087407699005, 360582087336871353, 360582087265774709, 360582087300245695, 360582087343286596, 360582087386617932]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595655195525969, 360595713924889064⟩, ⟨(-1289437687502931662), (-1285696006575113056)⟩, true⟩

def words04 : List Nat := [360582087387841620, 360582087342328583, 360582087224675300, 360582087219712773, 360582087214387873, 360582087182882795, 360582087184119783, 360582087100733425, 360582087044610274, 360582087190603523]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943A
