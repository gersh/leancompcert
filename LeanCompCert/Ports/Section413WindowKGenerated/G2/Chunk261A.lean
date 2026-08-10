import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360503975927615953, 360503979975803744⟩, ⟨2062155528833628676, 2062227000628616958⟩, true⟩

def state01 : KState := ⟨⟨360518493816987971, 360518497868403862⟩, ⟨1682970334355201073, 1683041890419413415⟩, true⟩

def words00 : List Nat := [360582989477656525, 360582987342032626, 360582984393109525, 360582980103569549, 360582975814301503, 360582970678116153, 360582966484004103, 360582963753743341, 360582961023657515, 360582957534831262]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592518447004437, 360592522501650436⟩, ⟨(-250125412488837301), (-250053772069821667)⟩, true⟩

def words01 : List Nat := [360582955066429774, 360582954061446860, 360582953514250203, 360582953771308851, 360582953771624596, 360582952791361994, 360582951811115454, 360582949962123989, 360582949232840193, 360582949599691483]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360521657857385197, 360521661915293137⟩, ⟨1600960685813930196, 1601032411450491638⟩, true⟩

def words02 : List Nat := [360582949599996692, 360582949227721652, 360582948087241467, 360582948026297976, 360582947965265372, 360582946776535357, 360582944127521715, 360582940750414432, 360582937373500934, 360582933725911220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360471051645205226, 360471055706342621⟩, ⟨2923505333202523360, 2923577143241158516⟩, true⟩

def words03 : List Nat := [360582931381399275, 360582928998216883, 360582926615179769, 360582923421078174, 360582919252711326, 360582914708159482, 360582910163849265, 360582906568408819, 360582903027738709, 360582898749312826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360534828706898435, 360534832771270260⟩, ⟨1256128516431219603, 1256200411033877301⟩, true⟩

def words04 : List Nat := [360582894471137096, 360582891653168959, 360582889569419344, 360582887900055625, 360582886230800429, 360582883225709226, 360582879760616428, 360582876511227437, 360582873261987030, 360582871027906355]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261A
