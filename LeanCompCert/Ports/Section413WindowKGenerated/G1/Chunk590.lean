import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500288520629785, 362500339491298530⟩, ⟨(-905335850353206865), (-903304463188068847)⟩, true⟩

def state01 : KState := ⟨⟨362480736372756075, 362480787361445899⟩, ⟨248253815222585476, 250286265722002366⟩, true⟩

def words00 : List Nat := [371285029758006386, 371285029760000683, 371285029629163206, 371285029617001027, 371285029674933370, 371285029676927843, 371285029400266312, 371285029098771024, 371285028796446497, 371285028782657931]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362466526703144601, 362466577709754269⟩, ⟨1086928383367182105, 1088961891410321161⟩, true⟩

def words01 : List Nat := [371285028927821569, 371285029145646020, 371285029363143250, 371285029365142451, 371285029286656207, 371285029170611146, 371285029053542836, 371285029054719150, 371285028746872025, 371285028436480978]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494576277961614, 362494627302428539⟩, ⟨(-568649721948159332), (-566615159878870036)⟩, true⟩

def words02 : List Nat := [371285028125221549, 371285028102314763, 371285028056521366, 371285028178915651, 371285028252360423, 371285028254369181, 371285028128868606, 371285028188391990, 371285028534314033, 371285028698984944]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491827101012176, 362491878143716884⟩, ⟨(-406368080067621401), (-404332441332313701)⟩, true⟩

def words03 : List Nat := [371285028801152544, 371285028903968310, 371285029134083192, 371285029222332309, 371285029395362920, 371285029569133515, 371285029690349091, 371285029692379530, 371285029691981912, 371285029810502130]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476260688561154, 362476311749028178⟩, ⟨512744130845521665, 514780818359705101⟩, true⟩

def words04 : List Nat := [371285030032997558, 371285030034993910, 371285029917592111, 371285029799421196, 371285029680531426, 371285029570262590, 371285029385309169, 371285029421843382, 371285029457685509, 371285029459753999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492765099332420, 362492816177854287⟩, ⟨(-461851378655330165), (-459813624912864987)⟩, true⟩

def words05 : List Nat := [371285029453067918, 371285029595067111, 371285030023207252, 371285030069568547, 371285030080981892, 371285030093041120, 371285030358013162, 371285030508632612, 371285030641853165, 371285030775898464]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492981224224501, 362493032320735262⟩, ⟨(-474695262800915955), (-472656446541143277)⟩, true⟩

def words06 : List Nat := [371285030907845511, 371285030909842152, 371285030694614243, 371285030732273638, 371285030854538776, 371285030856570246, 371285030741618425, 371285030628278625, 371285030685692568, 371285030823443171]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473684791663873, 362473735906201814⟩, ⟨665285291597371824, 667325172812259326⟩, true⟩

def words07 : List Nat := [371285031169110403, 371285031515614370, 371285031759403198, 371285031761400390, 371285031622943364, 371285031503966147, 371285031549533050, 371285031551530426, 371285031375605477, 371285031186716579]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475982533314282, 362476033665715433⟩, ⟨529552849047823947, 531593785713572611⟩, true⟩

def words08 : List Nat := [371285030996898335, 371285030894606964, 371285030714752970, 371285030769753274, 371285030786731377, 371285030788730489, 371285030483436181, 371285030250878471, 371285030017267787, 371285030006648139]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489950442490327, 362490001593072251⟩, ⟨(-295868143370853299), (-293826132312687849)⟩, true⟩

def words09 : List Nat := [371285029855896065, 371285029704433256, 371285029685350145, 371285029724517977, 371285029818940422, 371285029914142249, 371285030007272184, 371285030009279757, 371285029913252104, 371285029999828268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590
