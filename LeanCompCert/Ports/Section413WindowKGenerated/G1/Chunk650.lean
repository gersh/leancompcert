import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk650

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483972288491515, 362484034628131722⟩, ⟨94257286568673242, 96994141119598768⟩, true⟩

def state01 : KState := ⟨⟨362471785352661561, 362471847712279678⟩, ⟨886474800402714010, 889212953620954434⟩, true⟩

def words00 : List Nat := [371285526824385587, 371285526796385615, 371285526580419941, 371285526592516584, 371285526675961808, 371285526678175033, 371285526446553548, 371285526214264906, 371285525981074922, 371285525807243853]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473195912650328, 362473258292170201⟩, ⟨794814952264777883, 797554399396081267⟩, true⟩

def words01 : List Nat := [371285525624312160, 371285525652656408, 371285525679674924, 371285525681888589, 371285525393681821, 371285525179081580, 371285524963246469, 371285524958742345, 371285524771800481, 371285524585609083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484725048247886, 362484787447608128⟩, ⟨45090420060969933, 47831157314493761⟩, true⟩

def words02 : List Nat := [371285524398472137, 371285524278562232, 371285524039566417, 371285523898738352, 371285523757216616, 371285523554572871, 371285523172227285, 371285523027243667, 371285522969762032, 371285522972093973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485846681964697, 362485909101510644⟩, ⟨(-27816185477032156), (-25074135444245264)⟩, true⟩

def words03 : List Nat := [371285522962439499, 371285522947289627, 371285523149816164, 371285523252930846, 371285523427543159, 371285523602978159, 371285523720714527, 371285523722930891, 371285523580049591, 371285523588750320]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481248432015690, 362481310871274475⟩, ⟨271312590961340759, 274055923218821571⟩, true⟩

def words04 : List Nat := [371285523812845876, 371285523815066655, 371285523797061270, 371285523742853974, 371285523703573600, 371285523706015558, 371285523700815329, 371285523787399640, 371285523873179115, 371285523875474611]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500732771013912, 362500795230314108⟩, ⟨(-996235585475330638), (-993490949423393392)⟩, true⟩

def words05 : List Nat := [371285523845700818, 371285523881824981, 371285524152805865, 371285524212142377, 371285524233349233, 371285524255281421, 371285524475544731, 371285524611213881, 371285524847437532, 371285525084613560]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480052244411297, 362480114723689714⟩, ⟨349303867634079112, 352049803572516232⟩, true⟩

def words06 : List Nat := [371285525320920961, 371285525323136488, 371285525400580436, 371285525559194475, 371285525688093815, 371285525690309387, 371285525504660801, 371285525286922396, 371285525068310973, 371285525048010792]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473593466124425, 362473655965410376⟩, ⟨769680194191571553, 772427432119989063⟩, true⟩

def words07 : List Nat := [371285525119117437, 371285525274337655, 371285525438096416, 371285525440312125, 371285525289442146, 371285525185529127, 371285525169256308, 371285525171482882, 371285525036367629, 371285524856500112]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488514283590906, 362488576802705716⟩, ⟨(-201406017884624269), (-198657489393152047)⟩, true⟩

def words08 : List Nat := [371285524703156444, 371285524705598316, 371285524711620870, 371285524808952663, 371285524868127129, 371285524870382008, 371285524733174643, 371285524663911686, 371285524757246552, 371285524806432911]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490831613057321, 362490894152369124⟩, ⟨(-352276969615294434), (-349527126401993970)⟩, true⟩

def words09 : List Nat := [371285524854631512, 371285524903548765, 371285524988043392, 371285524990491168, 371285525032923647, 371285525084481037, 371285525136346189, 371285525138578072, 371285525069313715, 371285525154559536]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk650
