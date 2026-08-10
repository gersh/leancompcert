import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk860A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578645364090393, 360578693808561100⟩, ⟨307811023071020933, 310624547159546739⟩, true⟩

def state01 : KState := ⟨⟨360559232292985800, 360559280749245303⟩, ⟨1977409452567365498, 1980223990550513746⟩, true⟩

def words00 : List Nat := [360582305681003279, 360582305568283543, 360582305458971627, 360582305396010423, 360582305332710036, 360582305215246754, 360582304962417152, 360582304642063140, 360582304321498029, 360582303932486212]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552671995946519, 360552720463849914⟩, ⟨2541743015425855179, 2544558554959058071⟩, true⟩

def words01 : List Nat := [360582303665808641, 360582303534374352, 360582303402820885, 360582303188844518, 360582302903385355, 360582302584336364, 360582302264907743, 360582302080705867, 360582301817313799, 360582301474719004]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571359372497767, 360571407852083406⟩, ⟨934095125313103592, 936911669810024090⟩, true⟩

def words02 : List Nat := [360582301131842253, 360582300825465910, 360582300599360635, 360582300370004000, 360582300140559342, 360582299787614149, 360582299299278507, 360582298946270866, 360582298592907793, 360582298374805829]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562153823393650, 360562202314766351⟩, ⟨1726104759075919032, 1728922317671046484⟩, true⟩

def words03 : List Nat := [360582298249337422, 360582298017691220, 360582297785810610, 360582297662768895, 360582297623332764, 360582297550168586, 360582297476893332, 360582297280401603, 360582296948538283, 360582296716412923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564118032390430, 360564166535409907⟩, ⟨1557103855348241885, 1559922416091156907⟩, true⟩

def words04 : List Nat := [360582296483868387, 360582296361591153, 360582296218989530, 360582295969738928, 360582295720270304, 360582295437236891, 360582295221913594, 360582295047056617, 360582294872080046, 360582294628566109]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk860A
