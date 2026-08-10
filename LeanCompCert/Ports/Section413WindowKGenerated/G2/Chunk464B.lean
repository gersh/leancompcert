import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464B
