import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk132

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474526959937136, 362474529208537942⟩, ⟨130170585346414922, 130190668250870554⟩, true⟩

def state01 : KState := ⟨⟨362459079516080033, 362459081768202661⟩, ⟨334500983350839732, 334521112761582278⟩, true⟩

def words00 : List Nat := [371284395205945481, 371284395538434857, 371284395631235178, 371284395724147546, 371284397067228034, 371284397067663349, 371284399716324660, 371284403399418526, 371284405091999634, 371284405092408686]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362563883253170479, 362563885508861983⟩, ⟨(-1050636454340460168), (-1050616277766408340)⟩, true⟩

def words01 : List Nat := [371284404164513646, 371284405153506824, 371284411123021243, 371284411123416733, 371284409471751391, 371284406898594739, 371284407469556011, 371284407765678651, 371284413777879790, 371284419789342552]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362522785092157633, 362522787351429215⟩, ⟨(-507390455258854711), (-507370231338496527)⟩, true⟩

def words02 : List Nat := [371284425908884571, 371284426976921944, 371284430411896396, 371284433846555178, 371284438016244573, 371284438016641412, 371284436427119172, 371284434839063816, 371284437371273087, 371284440270230629]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362440173322813607, 362440175585649859⟩, ⟨586378827190610477, 586399098290306409⟩, true⟩

def words03 : List Nat := [371284447770577157, 371284455269955284, 371284461611211969, 371284462578477532, 371284465228562259, 371284467878436725, 371284472182540914, 371284472182937075, 371284468892724395, 371284465547756378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483074037633813, 362483076304021934⟩, ⟨18290753155032001, 18311071299084163⟩, true⟩

def words04 : List Nat := [371284464557115143, 371284464557551256, 371284465126926154, 371284466179646215, 371284466329560899, 371284466329957573, 371284460118334506, 371284457604540504, 371284458271256366, 371284458271667148]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507494503343933, 362507496773343837⟩, ⟨(-305500468404376995), (-305480102385871051)⟩, true⟩

def words05 : List Nat := [371284458167677444, 371284456923814486, 371284458615089519, 371284459111107355, 371284459820215865, 371284460529370149, 371284461269659505, 371284461270062934, 371284459057742494, 371284460795485013]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498371711523594, 362498373985057275⟩, ⟨(-184363525744523774), (-184343112849668992)⟩, true⟩

def words06 : List Nat := [371284467100527709, 371284467628787574, 371284468147827943, 371284468666928631, 371284469448453141, 371284469448897163, 371284473021959443, 371284477648517875, 371284482265516758, 371284483312700281]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488269781238837, 362488272058372223⟩, ⟨(-50091524546067142), (-50071063864955338)⟩, true⟩

def words07 : List Nat := [371284488243004408, 371284493172781305, 371284501792931295, 371284502858552659, 371284502858863483, 371284502637697903, 371284503299938596, 371284503300376042, 371284501646485036, 371284501930831756]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478612676864577, 362478614957585002⟩, ⟨77972358519519555, 77992866854632277⟩, true⟩

def words08 : List Nat := [371284501938253451, 371284501938651351, 371284495957282447, 371284494212024031, 371284492466832482, 371284492381025673, 371284489288366219, 371284485888539684, 371284483494893794, 371284483495346826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479662620995916, 362479664905303129⟩, ⟨64361079292518493, 64381635314238399⟩, true⟩

def words09 : List Nat := [371284488271060186, 371284493487688336, 371284497581457779, 371284497581857389, 371284497973478120, 371284499000887052, 371284505681429393, 371284505993000925, 371284505993302512, 371284505629762847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk132
