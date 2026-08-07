import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk426

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609211362401615, 360609222598295347⟩, ⟨(-1132540227398363752), (-1132216751013421294)⟩, true⟩

def state01 : KState := ⟨⟨360612063552141918, 360612074793509406⟩, ⟨(-1254073665871312285), (-1253749956276848045)⟩, true⟩

def words00 : List Nat := [360582645941538316, 360582646774269191, 360582647188633018, 360582647603037346, 360582647875161032, 360582648436528886, 360582649415971144, 360582650395478519, 360582650949766645, 360582651640889734]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360657778035456574, 360657789282303769⟩, ⟨(-3202106120302146110), (-3201782177190053796)⟩, true⟩

def words01 : List Nat := [360582652882484619, 360582654124191512, 360582655709093109, 360582657512495085, 360582658842975715, 360582660173444283, 360582661740543687, 360582663581961222, 360582665345119254, 360582667108324040]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612732123224725, 360612743375609450⟩, ⟨(-1282244079070686716), (-1281919899922403242)⟩, true⟩

def words02 : List Nat := [360582668594441009, 360582669701383435, 360582670792991443, 360582671884716467, 360582672585716718, 360582672739398301, 360582672739918122, 360582672550121297, 360582672535152887, 360582673241202038]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550895845823233, 360550907103676310⟩, ⟨1354296370576499802, 1354620782867877888⟩, true⟩

def words03 : List Nat := [360582674358187284, 360582675475231330, 360582676314038524, 360582676605642006, 360582676755369633, 360582676905251246, 360582677040015121, 360582677040596030, 360582676628221934, 360582675883762330]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603860831620866, 360603872094952978⟩, ⟨(-904318112288312670), (-903993466343120912)⟩, true⟩

def words04 : List Nat := [360582675139203174, 360582675117152755, 360582675839885527, 360582676562705571, 360582676821781825, 360582676822362842, 360582676534346563, 360582676329272660, 360582676467941975, 360582676965498965]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360592227214745969, 360592238483626135⟩, ⟨(-408213885495178081), (-407889002898682341)⟩, true⟩

def words05 : List Nat := [360582677044290584, 360582677123128127, 360582677123601528, 360582677329264870, 360582677329752304, 360582677309720960, 360582677289626667, 360582676931035259, 360582677090483807, 360582677315278026]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591851807386803, 360591863081738124⟩, ⟨(-392281232067915915), (-391956116044260213)⟩, true⟩

def words06 : List Nat := [360582677853466819, 360582677998402333, 360582677998920195, 360582677867365783, 360582677735732060, 360582677119978039, 360582677159923496, 360582677454802367, 360582677455328636, 360582677543174598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360618557988162208, 360618569268009986⟩, ⟨(-1531910478331306632), (-1531585127746672164)⟩, true⟩

def words07 : List Nat := [360582678138079743, 360582678733138254, 360582679751985498, 360582680532952181, 360582680834153659, 360582681135385971, 360582681985345689, 360582683113832890, 360582683955132661, 360582684796518066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624982919252602, 360624994204630879⟩, ⟨(-1806405289300176107), (-1806079702645745975)⟩, true⟩

def words08 : List Nat := [360582685281301337, 360582685281882878, 360582685707331726, 360582686194811792, 360582686540719794, 360582686901659098, 360582686902184338, 360582686867988465, 360582687347499288, 360582688339164019]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576646151253952, 360576657442118051⟩, ⟨257334513578327640, 257660334449870742⟩, true⟩

def words09 : List Nat := [360582689413421116, 360582690487738793, 360582691119619954, 360582691205667377, 360582691206154285, 360582691151073391, 360582691588448926, 360582691782175728, 360582691782694234, 360582691641988072]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk426
