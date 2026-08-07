import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk676

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468541570746155, 362468609204868735⟩, ⟨1137672495570530788, 1140760422919147990⟩, true⟩

def state01 : KState := ⟨⟨362489567898655051, 362489635553428559⟩, ⟨(-283739403199539785), (-280650079741294125)⟩, true⟩

def words00 : List Nat := [371285484110990415, 371285484082515472, 371285484039282598, 371285484111530784, 371285484148182587, 371285484150547068, 371285484198812355, 371285484334249029, 371285484536695794, 371285484600480943]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483590330339982, 362483658006144898⟩, ⟨120438657522019663, 123529403019576775⟩, true⟩

def words01 : List Nat := [371285484666001691, 371285484732278069, 371285484851027983, 371285484870461349, 371285484955679581, 371285485041812340, 371285485089468565, 371285485091777421, 371285484847827751, 371285484823699166]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471054087763118, 362471121784122621⟩, ⟨968224388503493661, 971316524008355433⟩, true⟩

def words02 : List Nat := [371285484931679153, 371285484933988073, 371285484777753613, 371285484622517502, 371285484466382555, 371285484373575718, 371285484210652417, 371285484139988994, 371285484068549114, 371285483997992330]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492698007316287, 362492765724560779⟩, ⟨(-495610475055898537), (-492516926992783413)⟩, true⟩

def words03 : List Nat := [371285483793240540, 371285483802078108, 371285483991674657, 371285484000120531, 371285484001925816, 371285483970759937, 371285484106648454, 371285484167892356, 371285484277129010, 371285484387398514]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474735442291581, 362474803180404933⟩, ⟨719391407057082322, 722486366793769912⟩, true⟩

def words04 : List Nat := [371285484452270409, 371285484454581668, 371285484273313957, 371285484173770078, 371285484073086974, 371285484026450428, 371285483709409659, 371285483393426273, 371285483076435248, 371285482949315411]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461293002871791, 362461360761723912⟩, ⟨1628916243291049795, 1632012606114464943⟩, true⟩

def words05 : List Nat := [371285482853438125, 371285482916355625, 371285482977662573, 371285482979972368, 371285482750085457, 371285482531227131, 371285482311158958, 371285482253890363, 371285481904979688, 371285481551054602]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469923745063201, 362469991524615489⟩, ⟨1044962324923101595, 1048060088425803603⟩, true⟩

def words06 : List Nat := [371285481196137160, 371285480954751995, 371285480636134192, 371285480507100989, 371285480377330363, 371285480222449902, 371285479830829807, 371285479636612382, 371285479441256254, 371285479334404551]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477055788269567, 362477123588929818⟩, ⟨562283243210773660, 565382435191819138⟩, true⟩

def words07 : List Nat := [371285479107278679, 371285478880134267, 371285478652021022, 371285478536831951, 371285478311570827, 371285478153500484, 371285477994636729, 371285477808788785, 371285477468822364, 371285477348315040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472643660719657, 362472711481965033⟩, ⟨860920530247634784, 864021115538391018⟩, true⟩

def words08 : List Nat := [371285477288526815, 371285477290838598, 371285477100466597, 371285476843514688, 371285476585706040, 371285476395401269, 371285476116579354, 371285476038238654, 371285475959119580, 371285475865412195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491884474604001, 362491952316709747⟩, ⟨(-441590506850289688), (-438488509412706516)⟩, true⟩

def words09 : List Nat := [371285475678419638, 371285475583726856, 371285475592206258, 371285475594539808, 371285475557830269, 371285475487022222, 371285475415276175, 371285475404026119, 371285475378985301, 371285475477233038]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk676
