import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk860

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

def state06 : KState := ⟨⟨360572062716028770, 360572111230747861⟩, ⟨873337225360842481, 876156792912537699⟩, true⟩

def words05 : List Nat := [360582294418919020, 360582294164717961, 360582293910165894, 360582293676784024, 360582293398712619, 360582293005842063, 360582292612742810, 360582292312464243, 360582292114584991, 360582291997572316]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569976324885891, 360570024851377821⟩, ⟨1052798872340144009, 1055619453120125435⟩, true⟩

def words06 : List Nat := [360582291880377610, 360582291695761024, 360582291434222740, 360582291275199833, 360582291115861247, 360582290864786427, 360582290551607955, 360582290160589062, 360582289769342034, 360582289513317175]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360537346865811460, 360537395403976556⟩, ⟨3861391423704775656, 3864213009253023194⟩, true⟩

def words07 : List Nat := [360582289371825830, 360582289232181942, 360582289092388495, 360582288866944732, 360582288506312376, 360582288056675657, 360582287606671740, 360582287291697196, 360582286874590177, 360582286354362860]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572371677785277, 360572420227635260⟩, ⟨846313694903216986, 849136286343723316⟩, true⟩

def words08 : List Nat := [360582285833866920, 360582285404372962, 360582285042471228, 360582284815580125, 360582284588608760, 360582284246709904, 360582284019800293, 360582283875754302, 360582283731347900, 360582283583267084]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545341860359150, 360545390422013217⟩, ⟨3173481422127840348, 3176305029839297318⟩, true⟩

def words09 : List Nat := [360582283469800911, 360582283288958369, 360582283107900461, 360582282915245615, 360582282790192245, 360582282610874236, 360582282431432756, 360582282149327087, 360582281732085524, 360582281305054324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk860
