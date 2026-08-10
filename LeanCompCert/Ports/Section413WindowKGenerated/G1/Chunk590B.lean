import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk590B
