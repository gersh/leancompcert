import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk241

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482236389102791, 362482244290335940⟩, ⟨68244943213518977, 68373693523702141⟩, true⟩

def state01 : KState := ⟨⟨362522834978718845, 362522842886754496⟩, ⟨(-910402735108721822), (-910273820823863798)⟩, true⟩

def words00 : List Nat := [371285081350190732, 371285081351038184, 371285082005438790, 371285083195726471, 371285084126927016, 371285084127688022, 371285084265608941, 371285085197647665, 371285087853997918, 371285089420667488]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362529400817962510, 362529408732925081⟩, ⟨(-1068688174212319716), (-1068559092885025760)⟩, true⟩

def words01 : List Nat := [371285090881314444, 371285092342103324, 371285095526886086, 371285097857890094, 371285100153197808, 371285102448585857, 371285104734739523, 371285105108050231, 371285106945366654, 371285108782969233]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362516894162052361, 362516902083794133⟩, ⟨(-766837362535926793), (-766708117659640233)⟩, true⟩

def words02 : List Nat := [371285112343238515, 371285114490654421, 371285116064143803, 371285117637745887, 371285119738827747, 371285120986479325, 371285123447111057, 371285125907860864, 371285128020939949, 371285129338459931]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362603272753204218, 362603280681804235⟩, ⟨(-2851564621684264069), (-2851435211283336679)⟩, true⟩

def words03 : List Nat := [371285132013492111, 371285134688685936, 371285139084674734, 371285141958296215, 371285144575116828, 371285147191976890, 371285151529439150, 371285155024394017, 371285159918268338, 371285164812068792]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362523085042199445, 362523092977668099⟩, ⟨(-915548438728179555), (-915418862483325071)⟩, true⟩

def words04 : List Nat := [371285169698500878, 371285172297155869, 371285175585769024, 371285178874502791, 371285182258110780, 371285183354868230, 371285184445022074, 371285185535328883, 371285187433824479, 371285189004230837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488636890458401, 362488644832780758⟩, ⟨(-83194215246770299), (-83064473450358133)⟩, true⟩

def words05 : List Nat := [371285192293315861, 371285195582442971, 371285198734828231, 371285200267541500, 371285202310564616, 371285204353798768, 371285206437277735, 371285206589969048, 371285206732849761, 371285206876013640]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362510142844357617, 362510150793486111⟩, ⟨(-602761118658639993), (-602631212390798095)⟩, true⟩

def words06 : List Nat := [371285208344237793, 371285208962097495, 371285211055469796, 371285213148983877, 371285214970600722, 371285214971361874, 371285215250739438, 371285215651123148, 371285217767775601, 371285218800089446]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362546485393295315, 362546493349363014⟩, ⟨(-1481427576374853638), (-1481297502351424848)⟩, true⟩

def words07 : List Nat := [371285219514606712, 371285220229303784, 371285222155182487, 371285223426181262, 371285225195899800, 371285226965771135, 371285228725286165, 371285229544510151, 371285232078683540, 371285234613067931]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362522870731647503, 362522878694486369⟩, ⟨(-910181191299607935), (-910050953513600075)⟩, true⟩

def words08 : List Nat := [371285238861959104, 371285241129158667, 371285243392697053, 371285245656305487, 371285248031781696, 371285249728477629, 371285252502986242, 371285255277565843, 371285257736545255, 371285259292497465]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362553658444920890, 362553666414671869⟩, ⟨(-1655085916856505095), (-1654955511833931935)⟩, true⟩

def words09 : List Nat := [371285261886332846, 371285264480381569, 371285268186646469, 371285269615063554, 371285270791317356, 371285271967704357, 371285274856581063, 371285276995869126, 371285279822404966, 371285282649049212]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk241
