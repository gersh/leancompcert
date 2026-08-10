import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553165428873917, 360553171907261784⟩, ⟨920898253368492709, 921041496451085255⟩, true⟩

def state01 : KState := ⟨⟨360558445538762309, 360558452021258916⟩, ⟨748121141162231543, 748264518621141359⟩, true⟩

def words00 : List Nat := [360581337452902396, 360581337219784940, 360581336316350911, 360581334694568743, 360581333072807458, 360581331038420102, 360581329629663799, 360581329153242145, 360581328676798691, 360581327732620003]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360645877785143331, 360645884271763030⟩, ⟨(-2112435624910979288), (-2112292112565689958)⟩, true⟩

def words01 : List Nat := [360581327033651323, 360581326309940719, 360581325793827163, 360581325874021071, 360581325874427145, 360581325156186475, 360581324650930518, 360581325692989368, 360581327666404117, 360581329639796841]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576169974462496, 360576176465237415⟩, ⟨168498892160776866, 168642540485445920⟩, true⟩

def words02 : List Nat := [360581331017805713, 360581331464293264, 360581332494440541, 360581333524657327, 360581333562456348, 360581333562892922, 360581332669333700, 360581331308634149, 360581329947934840, 360581329002374154]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360525233808211965, 360525240303104154⟩, ⟨1836099293099717216, 1836243076203636080⟩, true⟩

def words03 : List Nat := [360581329340245681, 360581329835598708, 360581329862793079, 360581329863231789, 360581329629668238, 360581329159107633, 360581328688445328, 360581328625634760, 360581327632020963, 360581325919359611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586328957499271, 360586335456514270⟩, ⟨(-164435817585565630), (-164291899480606570)⟩, true⟩

def words04 : List Nat := [360581324206704563, 360581322997499252, 360581322604818551, 360581322754656562, 360581322755059598, 360581321978345900, 360581321235016010, 360581320150125886, 360581319065174288, 360581319063137561]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327A
