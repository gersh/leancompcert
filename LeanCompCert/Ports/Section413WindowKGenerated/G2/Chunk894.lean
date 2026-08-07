import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk894

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594487931376959, 360594540439311716⟩, ⟨(-1119846681461592013), (-1116676743548369569)⟩, true⟩

def state01 : KState := ⟨⟨360580818534313416, 360580871054389350⟩, ⟨102202302080332736, 105373325476758508⟩, true⟩

def words00 : List Nat := [360582049917835942, 360582049923209703, 360582049924361558, 360582049843690639, 360582049762787573, 360582049650670417, 360582049618811592, 360582049637744410, 360582049638893219, 360582049595106013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602517551634615, 360602570083899726⟩, ⟨(-1838057170267122073), (-1834885056975504219)⟩, true⟩

def words01 : List Nat := [360582049582985600, 360582049541633736, 360582049582043207, 360582049683122550, 360582049684323061, 360582049677255178, 360582049786485241, 360582050001249336, 360582050231778555, 360582050462591807]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587987123455638, 360588039667998802⟩, ⟨(-538778090022091521), (-535604878768055871)⟩, true⟩

def words02 : List Nat := [360582050614959050, 360582050642522860, 360582050770470296, 360582050898810718, 360582050934923204, 360582050936213090, 360582050886005110, 360582050756748947, 360582050627248858, 360582050638705067]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565929848659692, 360565982405359419⟩, ⟨1433988921060964624, 1437163219538063616⟩, true⟩

def words03 : List Nat := [360582050831579154, 360582051024718721, 360582051140369881, 360582051166711590, 360582051167791655, 360582051140736294, 360582051127023458, 360582051128313346, 360582051045432440, 360582050867116330]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590802862728993, 360590855431595212⟩, ⟨(-790814420414580036), (-787639033704467274)⟩, true⟩

def words04 : List Nat := [360582050688512053, 360582050496062088, 360582050366133649, 360582050361293190, 360582050356352680, 360582050237750778, 360582050121781551, 360582050065158498, 360582050074934421, 360582050174709270]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360579773071758477, 360579825652943674⟩, ⟨195830034642806046, 199006523344411744⟩, true⟩

def words05 : List Nat := [360582050210228086, 360582050245886560, 360582050246952607, 360582050300008345, 360582050338945537, 360582050378092489, 360582050379241960, 360582050355694558, 360582050207075729, 360582050183721054]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577510383481148, 360577562976809353⟩, ⟨398244346217232751, 401421921292342421⟩, true⟩

def words06 : List Nat := [360582050236016013, 360582050240073809, 360582050241231137, 360582050150958170, 360582050060477273, 360582049913319458, 360582049862999437, 360582049809971483, 360582049756814777, 360582049641851181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602087164966795, 360602139770477128⟩, ⟨(-1800797502775379459), (-1797618837704504131)⟩, true⟩

def words07 : List Nat := [360582049592752731, 360582049529628534, 360582049502725298, 360582049610853753, 360582049612045331, 360582049613309052, 360582049739041662, 360582049927597480, 360582050153163215, 360582050379011851]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585617423187397, 360585670040999220⟩, ⟨(-327118687440280297), (-323938921571362803)⟩, true⟩

def words08 : List Nat := [360582050509228830, 360582050514805122, 360582050599782079, 360582050685136019, 360582050690137545, 360582050691428289, 360582050604908726, 360582050438740033, 360582050272301211, 360582050247706360]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569243705856612, 360569296335820064⟩, ⟨1138303593645360900, 1141484447024440782⟩, true⟩

def words09 : List Nat := [360582050413900596, 360582050580344812, 360582050667363748, 360582050688208642, 360582050689307553, 360582050624866396, 360582050570571385, 360582050571862418, 360582050493154486, 360582050351987935]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk894
