import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk130

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362403304759791096, 362403306937820551⟩, ⟨1049945608240170422, 1049964766629526180⟩, true⟩

def state01 : KState := ⟨⟨362552643400581340, 362552645582085089⟩, ⟨(-891977362347471304), (-891958158774184666)⟩, true⟩

def words00 : List Nat := [371284067246263071, 371284066944851745, 371284068189450500, 371284071765770437, 371284073801114651, 371284073801509633, 371284074072275440, 371284077160745418, 371284086153645199, 371284091423390586]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362513762888924576, 362513765073968413⟩, ⟨(-385993784451955128), (-385974534804214974)⟩, true⟩

def words01 : List Nat := [371284096686963843, 371284101949855036, 371284107343894078, 371284109803660192, 371284113409304342, 371284117014545300, 371284120616037396, 371284120616426609, 371284120331947652, 371284122609119000]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464065112178020, 362464067300686131⟩, ⟨261544762232311370, 261564057002971210⟩, true⟩

def words02 : List Nat := [371284129232492575, 371284129924849054, 371284130552290446, 371284131179771835, 371284133557763596, 371284133809897769, 371284136465416671, 371284139120677423, 371284141287774043, 371284141288176766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362603865891841964, 362603868083873902⟩, ⟨(-1560548343612162199), (-1560529002908376209)⟩, true⟩

def words03 : List Nat := [371284143228692096, 371284146709360610, 371284156071882705, 371284161583860651, 371284165470891319, 371284169357440925, 371284179122618871, 371284186435576234, 371284195613883552, 371284204790958606]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362579168497251395, 362579170692804449⟩, ⟨(-1238758827586088305), (-1238739440948826069)⟩, true⟩

def words04 : List Nat := [371284212684734012, 371284212752241781, 371284218694231498, 371284224635506489, 371284232313870338, 371284234801341788, 371284237288100713, 371284239774620013, 371284248129830794, 371284255403481882]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488139006758777, 362488141205818052⟩, ⟨(-49988685433761864), (-49969253022516970)⟩, true⟩

def words05 : List Nat := [371284267421230325, 371284279437293360, 371284291017028053, 371284295929495009, 371284301100812218, 371284306271531004, 371284314430546012, 371284314782467258, 371284315075749912, 371284315369126948]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362547662234519883, 362547664437077722⟩, ⟨(-827292280049131055), (-827272801928957703)⟩, true⟩

def words06 : List Nat := [371284320025351743, 371284322560179031, 371284330950334937, 371284339339368407, 371284346954918553, 371284348072358529, 371284354214925038, 371284360356755840, 371284368889471743, 371284373732316881]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362519797553635919, 362519799759756407⟩, ⟨(-462737008247394588), (-462717483545277932)⟩, true⟩

def words07 : List Nat := [371284378576353985, 371284383419787202, 371284391895047798, 371284397451345180, 371284404765775941, 371284412079240141, 371284419337792395, 371284421099812315, 371284423804870599, 371284426509733834]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505014214891991, 362505016424500674⟩, ⟨(-269318887950377421), (-269299317604579441)⟩, true⟩

def words08 : List Nat := [371284434016992665, 371284435141760545, 371284435142058260, 371284435042107545, 371284436567691184, 371284436568125495, 371284438057310415, 371284440787150863, 371284443519761071, 371284445091706802]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362565030927727470, 362565033140863331⟩, ⟨(-1055330578992558222), (-1055310962457680342)⟩, true⟩

def words09 : List Nat := [371284448967865616, 371284452843627538, 371284462546322806, 371284464487457546, 371284465052627120, 371284465617832072, 371284468572536010, 371284468901481783, 371284475051689954, 371284481201129137]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk130
