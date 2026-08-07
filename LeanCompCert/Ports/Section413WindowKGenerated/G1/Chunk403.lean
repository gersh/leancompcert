import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk403

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362453788477588139, 362453811537517956⟩, ⟨1266903302731871829, 1267531269855165505⟩, true⟩

def state01 : KState := ⟨⟨362483559160355277, 362483582232110578⟩, ⟨67046743320761296, 67675187072481008⟩, true⟩

def words00 : List Nat := [371285263146808209, 371285262925382543, 371285262397224222, 371285262330492275, 371285262263325613, 371285262098278017, 371285261421846275, 371285261133118027, 371285261099187353, 371285261100556931]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469311861803372, 362469334945648872⟩, ⟨641434134557639172, 642063065723040676⟩, true⟩

def words01 : List Nat := [371285261059907660, 371285261017199889, 371285261086709487, 371285261088165871, 371285260894440669, 371285260727577520, 371285260560288794, 371285260358331732, 371285259522080221, 371285259128826527]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362457363254119252, 362457386349733848⟩, ⟨1123296710596365143, 1123926116353064253⟩, true⟩

def words02 : List Nat := [371285258868169914, 371285258869492378, 371285258184672323, 371285257500034861, 371285256814934863, 371285256321054637, 371285255702572987, 371285255331953680, 371285254960904004, 371285254589663257]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486043065191228, 362486066172749678⟩, ⟨(-33421489587459717), (-32791602073712589)⟩, true⟩

def words03 : List Nat := [371285253899573766, 371285253721295728, 371285253886166396, 371285253887513092, 371285253816538928, 371285253648500511, 371285253516973341, 371285253518446078, 371285253290709073, 371285253312332889]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467834901703670, 362467858021210289⟩, ⟨701104957214746657, 701735326778354269⟩, true⟩

def words04 : List Nat := [371285253313342249, 371285253171534086, 371285252367239781, 371285252177720745, 371285251987545928, 371285251982861989, 371285251159660274, 371285250336653205, 371285249513126921, 371285249231291537]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362455648895466132, 362455672026900488⟩, ⟨1192982133584574720, 1193612984493207984⟩, true⟩

def words05 : List Nat := [371285248983964543, 371285249168189991, 371285249351573876, 371285249352897647, 371285248718374938, 371285248117663204, 371285247527630597, 371285247528958036, 371285246915376571, 371285246184098041]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474902712421362, 362474925855723445⟩, ⟨415926641635271781, 416557971585592227⟩, true⟩

def words06 : List Nat := [371285245452255670, 371285245334561233, 371285245229791791, 371285245445039144, 371285245551493308, 371285245552817329, 371285244841706880, 371285244610398307, 371285244378413157, 371285244358859081]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481782489225295, 362481805644568212⟩, ⟨138170654294956984, 138802470395961098⟩, true⟩

def words07 : List Nat := [371285244104257221, 371285243849740861, 371285243851906458, 371285243853378670, 371285243806300984, 371285243793584520, 371285243780385347, 371285243749459993, 371285243134471491, 371285243050967320]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467875309444398, 362467898476592767⟩, ⟨699777967984499976, 700410260851026426⟩, true⟩

def words08 : List Nat := [371285243195429864, 371285243196754709, 371285242696751012, 371285242074316062, 371285241451387076, 371285240936072458, 371285240156449429, 371285239990050471, 371285239823222939, 371285239656608886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489495335897179, 362489518515038971⟩, ⟨(-173545285463535956), (-172912508124931230)⟩, true⟩

def words09 : List Nat := [371285239228179711, 371285239182931896, 371285239600194396, 371285239601522316, 371285239434522202, 371285239171202340, 371285238907385652, 371285238804525180, 371285238500953814, 371285238608399905]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk403
