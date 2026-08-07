import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598138060987374, 360598188635397882⟩, ⟨(-1411865470475329764), (-1408866847703623062)⟩, true⟩

def state01 : KState := ⟨⟨360603506220877817, 360603556807347642⟩, ⟨(-1883289701038534596), (-1880290019399383168)⟩, true⟩

def words00 : List Nat := [360582142573375504, 360582142692508112, 360582142940952712, 360582143189777645, 360582143362328001, 360582143453352663, 360582143479292964, 360582143505393149, 360582143640896536, 360582143886194263]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590971705031364, 360591022303401214⟩, ⟨(-782526190387836459), (-779525463746928045)⟩, true⟩

def words01 : List Nat := [360582144260614193, 360582144635269191, 360582144911417590, 360582145145934676, 360582145271631489, 360582145397637334, 360582145626709267, 360582145799709798, 360582145901912650, 360582146004295682]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606827259826445, 360606877870155898⟩, ⟨(-2174980687376105098), (-2171978910385899632)⟩, true⟩

def words02 : List Nat := [360582146197207399, 360582146517290023, 360582146916211295, 360582147315373779, 360582147603747230, 360582147762719253, 360582148015298984, 360582148268251060, 360582148517709279, 360582148800574704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599359483779723, 360599410106159919⟩, ⟨(-1519022842669928370), (-1516020007202469456)⟩, true⟩

def words03 : List Nat := [360582149017280996, 360582149234108789, 360582149580161552, 360582149991746512, 360582150318616514, 360582150645700375, 360582150873454022, 360582151027331224, 360582151224839596, 360582151422775139]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596008127525804, 360596058761834476⟩, ⟨(-1224711359236921690), (-1221707475913652346)⟩, true⟩

def words04 : List Nat := [360582151609155622, 360582151695582161, 360582151696729286, 360582151677793481, 360582151658651710, 360582151652507606, 360582151801108602, 360582151949948873, 360582152016323749, 360582152175957097]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk878
