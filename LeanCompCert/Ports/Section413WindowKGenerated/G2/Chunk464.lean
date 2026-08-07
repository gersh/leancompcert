import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605665074736713, 360605678498530475⟩, ⟨(-1050812697799003164), (-1050391795818071740)⟩, true⟩

def state01 : KState := ⟨⟨360557578063723439, 360557591493588843⟩, ⟨1180483629956108953, 1180904813690436097⟩, true⟩

def words00 : List Nat := [360583041488969326, 360583041489606011, 360583041282724474, 360583041055969635, 360583040829049624, 360583040485043882, 360583039677409636, 360583038609003646, 360583037540525298, 360583036544519471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360512498208129131, 360512511643984757⟩, ⟨3273041783845767888, 3273463245617080602⟩, true⟩

def words01 : List Nat := [360583035996779601, 360583035912144604, 360583035827449227, 360583035498390152, 360583034961734725, 360583034308208702, 360583033654534235, 360583032830703448, 360583031543483047, 360583030024976078]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360535280833627872, 360535294275490309⟩, ⟨2215390798009876571, 2215812538647612657⟩, true⟩

def words02 : List Nat := [360583028506385981, 360583027312073265, 360583026353741881, 360583025532224351, 360583024710682110, 360583023494765663, 360583021940040799, 360583020543317852, 360583019146468614, 360583018000208113]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360543750815217883, 360543764263162599⟩, ⟨1821964917202972084, 1822386940268924504⟩, true⟩

def words03 : List Nat := [360583016972952819, 360583015482430800, 360583013991851092, 360583012808525479, 360583011893954135, 360583010748724986, 360583009603471794, 360583008165857367, 360583006858958752, 360583006014675712]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559898292854954, 360559911746796380⟩, ⟨1072020356613533643, 1072442658197272221⟩, true⟩

def words04 : List Nat := [360583005170210129, 360583004788227752, 360583004339255203, 360583003636214367, 360583002933107341, 360583001913776842, 360583001126650334, 360583000801930118, 360583000477162190, 360582999855691908]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570869283100988, 360570882743065225⟩, ⟨562333933083384397, 562756514455993327⟩, true⟩

def words05 : List Nat := [360582999359164957, 360582999325049235, 360582999290739534, 360582999138147152, 360582998522911690, 360582997515111053, 360582996507231733, 360582995961686961, 360582995713291752, 360582995453234317]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580796960455142, 360580810426488889⟩, ⟨100873111029939880, 101295974422793486⟩, true⟩

def words06 : List Nat := [360582995193096698, 360582994606040711, 360582993884414711, 360582993497352272, 360582993110133008, 360582992606259262, 360582992119175773, 360582991400460225, 360582990681653913, 360582990240872853]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562657195654524, 360562670667703311⟩, ⟨943982534938135128, 944405677879756926⟩, true⟩

def words07 : List Nat := [360582990609356231, 360582991024851226, 360582991081670655, 360582991082309794, 360582990943737888, 360582990424824854, 360582989905740740, 360582989848496354, 360582989642867694, 360582989206384029]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588284227643610, 360588297705708838⟩, ⟨(-247287220145823249), (-246863797529974107)⟩, true⟩

def words08 : List Nat := [360582988769763397, 360582988811220821, 360582988970609612, 360582989130112688, 360582989130706208, 360582988898861685, 360582988599589905, 360582988134257697, 360582987668755213, 360582987779109497]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583166446724785, 360583179930864685⟩, ⟨(-9351994010004352), (-8928288953876336)⟩, true⟩

def words09 : List Nat := [360582987779677768, 360582987663749846, 360582987635502362, 360582988122705834, 360582988326473939, 360582988530336031, 360582988530908207, 360582988376459517, 360582987923921720, 360582987928779701]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464
