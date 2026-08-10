import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417A

def state06 : KState := ⟨⟨360586152597062000, 360586163376630505⟩, ⟨(-155090862918151652), (-154786635019242116)⟩, true⟩

def words05 : List Nat := [360582454797380367, 360582454958666675, 360582455478649684, 360582456284692746, 360582456695189788, 360582457105758095, 360582457193091588, 360582457193659473, 360582456799467544, 360582456888878315]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601984214116625, 360601994999041447⟩, ⟨(-816162871553705682), (-815858419948237682)⟩, true⟩

def words06 : List Nat := [360582457550213226, 360582458440773363, 360582459044717676, 360582459648695170, 360582460106178808, 360582460849455887, 360582461680356575, 360582462511323897, 360582462836137379, 360582463304326257]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360651243673438123, 360651254463720609⟩, ⟨(-2874036391446105734), (-2873731716023962946)⟩, true⟩

def words07 : List Nat := [360582464344172188, 360582465384134807, 360582466756170120, 360582467558436258, 360582467858623888, 360582468158850617, 360582469030589012, 360582470343473869, 360582471990274276, 360582473637124215]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608853005679629, 360608863801380738⟩, ⟨(-1102887930972844858), (-1102583029134389762)⟩, true⟩

def words08 : List Nat := [360582474934265249, 360582476064509643, 360582477043625050, 360582478022851900, 360582478748580232, 360582479288427373, 360582479539488707, 360582479790595741, 360582479904355821, 360582480536344382]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360530181825689547, 360530192626741407⟩, ⟨2185276285655058605, 2185581411128186481⟩, true⟩

def words09 : List Nat := [360582481338876022, 360582482141477327, 360582482657814325, 360582482658382682, 360582482605477442, 360582482239495847, 360582481873366748, 360582481478114175, 360582480513683529, 360582479263371268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417B
