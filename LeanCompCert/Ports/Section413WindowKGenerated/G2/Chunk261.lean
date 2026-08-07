import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261

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

def state06 : KState := ⟨⟨360539097064815720, 360539101132456853⟩, ⟨1144537815738587665, 1144609795849992995⟩, true⟩

def words05 : List Nat := [360582869191255581, 360582866405046345, 360582863618979000, 360582862291544853, 360582861714067128, 360582860761396640, 360582859808760188, 360582858119149022, 360582857001780198, 360582855329545921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547932173714331, 360547936244586183⟩, ⟨913384802555430268, 913456867198257256⟩, true⟩

def words06 : List Nat := [360582853657326410, 360582853442754218, 360582852275824399, 360582849995740730, 360582847715775362, 360582845061530186, 360582843563997519, 360582843129100680, 360582842694203340, 360582840977761509]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617227355704516, 360617231429819619⟩, ⟨(-900514046287431406), (-900441896752647552)⟩, true⟩

def words07 : List Nat := [360582839766884048, 360582839889818703, 360582839974276564, 360582839974620221, 360582839439235407, 360582837630936471, 360582835822710300, 360582835848874245, 360582837162963445, 360582838477038876]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360637458277427228, 360637462354811248⟩, ⟨(-1430453527597692756), (-1430381292466646864)⟩, true⟩

def words08 : List Nat := [360582839067124644, 360582840026456195, 360582842440507554, 360582844854474681, 360582846895135427, 360582847483135776, 360582847483447400, 360582846771987736, 360582846802966509, 360582848888640936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360527564405319391, 360527568485937306⟩, ⟨1448439058774418800, 1448511378617481072⟩, true⟩

def words09 : List Nat := [360582851190736134, 360582853492719197, 360582855060030507, 360582856678516928, 360582857362542226, 360582858046604553, 360582858393598556, 360582858393942056, 360582857289681565, 360582855179777668]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261
