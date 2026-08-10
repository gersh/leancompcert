import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878A

def state06 : KState := ⟨⟨360613449524041704, 360613500170292347⟩, ⟨(-2757010767745047147), (-2754005835260625989)⟩, true⟩

def words05 : List Nat := [360582152422668393, 360582152669745549, 360582153045851795, 360582153426808172, 360582153697594687, 360582153968479616, 360582154163381619, 360582154422669710, 360582154780461763, 360582155138534678]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606167975394913, 360606218633689592⟩, ⟨(-2117326086055677587), (-2114320095322591293)⟩, true⟩

def words06 : List Nat := [360582155431586135, 360582155624573439, 360582155895034383, 360582156165884731, 360582156403854536, 360582156512667034, 360582156539164226, 360582156565791463, 360582156721520529, 360582156996797756]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586124416170739, 360586175086400786⟩, ⟨(-356012749076988274), (-353005709522763788)⟩, true⟩

def words07 : List Nat := [360582157268598665, 360582157540618143, 360582157723012420, 360582157817742521, 360582157830722152, 360582157844046130, 360582157986317424, 360582158132123186, 360582158178967785, 360582158225992703]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620050453985689, 360620101136154309⟩, ⟨(-3337628242360281520), (-3334620153588262460)⟩, true⟩

def words08 : List Nat := [360582158402048733, 360582158660323793, 360582158979379085, 360582159298668379, 360582159502775369, 360582159577647242, 360582159781582908, 360582159985885793, 360582160297948801, 360582160730952545]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603940797913301, 360603991492143377⟩, ⟨(-1921628432050918864), (-1918619283138432810)⟩, true⟩

def words09 : List Nat := [360582161098966234, 360582161467132482, 360582161873667200, 360582162361162364, 360582162815814754, 360582163270663430, 360582163653786469, 360582163945734274, 360582164195098682, 360582164444861339]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878B
