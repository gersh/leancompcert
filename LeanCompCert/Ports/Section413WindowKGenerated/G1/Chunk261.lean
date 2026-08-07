import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk261

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362449510373523232, 362449519702891138⟩, ⟨938014706783713797, 938179323803594999⟩, true⟩

def state01 : KState := ⟨⟨362435409989861338, 362435419326602411⟩, ⟨1306099273119244364, 1306264082616831210⟩, true⟩

def words00 : List Nat := [371285463894242727, 371285463705766264, 371285461885129107, 371285459608370505, 371285457331460476, 371285455158068839, 371285452423666456, 371285451154734665, 371285449885635707, 371285448590586204]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494955304955990, 362494964649180330⟩, ⟨(-248834771122020321), (-248669766198739673)⟩, true⟩

def words01 : List Nat := [371285446675125698, 371285446224795768, 371285446787225166, 371285446788057903, 371285446495367422, 371285445980132726, 371285445464622656, 371285445100768480, 371285444366230684, 371285444731635109]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362441544574801935, 362441553926494666⟩, ⟨1146482022650662918, 1146647222686192338⟩, true⟩

def words02 : List Nat := [371285445091580174, 371285445092408001, 371285443779219636, 371285443732212281, 371285443684799359, 371285443665067897, 371285441694177846, 371285439734144967, 371285437773916965, 371285436330730648]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362425059468110127, 362425068827256915⟩, ⟨1577374182839348211, 1577539577687198171⟩, true⟩

def words03 : List Nat := [371285434651979270, 371285433583637392, 371285432515106670, 371285431474241517, 371285428742948633, 371285426454951356, 371285424166678185, 371285423077641920, 371285420774676226, 371285418466801185]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362451322951566224, 362451332318123995⟩, ⟨890848909095173799, 891014497704155917⟩, true⟩

def words04 : List Nat := [371285416158743745, 371285415312650759, 371285413739041549, 371285413122232898, 371285412505217985, 371285411594514517, 371285409201267441, 371285407555416585, 371285405909273342, 371285405530273294]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461943349347221, 362461952723474350⟩, ⟨613158411546076365, 613324198131869749⟩, true⟩

def words05 : List Nat := [371285404227953160, 371285402799694274, 371285401402323959, 371285401403244981, 371285400700992732, 371285400441966462, 371285400182684834, 371285399918122319, 371285398733299594, 371285397838081838]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362448654207451371, 362448663588959727⟩, ⟨960976418354342176, 961142398071418024⟩, true⟩

def words06 : List Nat := [371285397505513242, 371285397506342235, 371285396346309203, 371285394977029104, 371285393607544321, 371285392681480592, 371285391244698483, 371285391094012199, 371285390943058783, 371285390466990733]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505088678850770, 362505098067859581⟩, ⟨(-516196209871427191), (-516030033829972205)⟩, true⟩

def words07 : List Nat := [371285389119005988, 371285389174787376, 371285389837475683, 371285389838306117, 371285388936187634, 371285387771013389, 371285386897119987, 371285386898033392, 371285387217644119, 371285387971460285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496439304321871, 362496448700812642⟩, ⟨(-289742112176256244), (-289575740218626660)⟩, true⟩

def words08 : List Nat := [371285388736566940, 371285388737402469, 371285389786443425, 371285391039979394, 371285392735822171, 371285392736651971, 371285392490669367, 371285391832330509, 371285391970562884, 371285392393675892]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362447466572368332, 362447475976337645⟩, ⟨993291385027146488, 993457952886032498⟩, true⟩

def words09 : List Nat := [371285393563396447, 371285394733370962, 371285395897844921, 371285395898689210, 371285396059495385, 371285396266131329, 371285396935209468, 371285396936039688, 371285395665190300, 371285394218814212]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk261
