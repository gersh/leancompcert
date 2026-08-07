import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478828026624819, 362478929045318546⟩, ⟨510822734989859349, 516416105867608583⟩, true⟩

def state01 : KState := ⟨⟨362493784681185137, 362493885725294768⟩, ⟨(-715673998710395525), (-710078543603481683)⟩, true⟩

def words00 : List Nat := [371285226774335806, 371285226777466155, 371285226891333747, 371285227024739606, 371285227103076512, 371285227105917158, 371285227044427160, 371285227090542792, 371285227283826307, 371285227392344268]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494318558930636, 362494419628921879⟩, ⟨(-759424321091822111), (-753826743301466663)⟩, true⟩

def words01 : List Nat := [371285227499991540, 371285227608626164, 371285227864765316, 371285228047863141, 371285228261866432, 371285228477013719, 371285228690303565, 371285228744002930, 371285228858020006, 371285228973561649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486732639724511, 362486833735023947⟩, ⟨(-137169157552032016), (-131569503853720252)⟩, true⟩

def words02 : List Nat := [371285229236211998, 371285229301645505, 371285229360212735, 371285229419758986, 371285229494019594, 371285229520992265, 371285229622334912, 371285229724792849, 371285229812723575, 371285229835231750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506367812551963, 362506468933579365⟩, ⟨(-1747961815426293710), (-1742360051131373306)⟩, true⟩

def words03 : List Nat := [371285230005348353, 371285230176973068, 371285230408318968, 371285230442471543, 371285230452841654, 371285230464049975, 371285230622740926, 371285230736162573, 371285230996965742, 371285231259110120]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489885302781670, 362489986449446398⟩, ⟨(-395665923638066619), (-390062055927687129)⟩, true⟩

def words04 : List Nat := [371285231487750015, 371285231607083987, 371285231824266378, 371285232042910944, 371285232292537053, 371285232344989816, 371285232368072946, 371285232392119295, 371285232490613249, 371285232551798257]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489501501660703, 362489602673878920⟩, ⟨(-364106991614832768), (-358501027109400966)⟩, true⟩

def words05 : List Nat := [371285232760225245, 371285232969778680, 371285233177089124, 371285233261962858, 371285233391456062, 371285233522393894, 371285233774933155, 371285233848234694, 371285233903604480, 371285233960030571]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494700807885125, 362494802005570993⟩, ⟨(-790775819610560577), (-785167765099418951)⟩, true⟩

def words06 : List Nat := [371285234055128719, 371285234089527327, 371285234253706094, 371285234419079848, 371285234559349151, 371285234562193142, 371285234645847417, 371285234764394129, 371285234952971497, 371285235072487451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493256180143210, 362493357403769051⟩, ⟨(-672197082804777597), (-666586899276693835)⟩, true⟩

def words07 : List Nat := [371285235162230596, 371285235252922595, 371285235490925224, 371285235656013901, 371285235820312106, 371285235985640401, 371285236148331107, 371285236151174056, 371285236214739158, 371285236317290126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494274201478978, 362494375450448748⟩, ⟨(-755689927400936103), (-750077663510822243)⟩, true⟩

def words08 : List Nat := [371285236552356395, 371285236739614979, 371285236925976994, 371285237113269093, 371285237344987116, 371285237503739966, 371285237740993469, 371285237979422759, 371285238187625527, 371285238301875691]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500755160228887, 362500856434879085⟩, ⟨(-1287738912959932357), (-1282124540831428741)⟩, true⟩

def words09 : List Nat := [371285238545674403, 371285238790910909, 371285239072219251, 371285239156633070, 371285239226946053, 371285239298224191, 371285239494970036, 371285239619082388, 371285239811234080, 371285240004618414]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820
