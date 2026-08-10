import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk611A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362517292252586856, 362517347068092223⟩, ⟨(-1959100892338052965), (-1956838597233367277)⟩, true⟩

def state01 : KState := ⟨⟨362488273222608483, 362488328056834083⟩, ⟨(-185962782790973068), (-183699343788006002)⟩, true⟩

def words00 : List Nat := [371285321311003123, 371285321519917236, 371285321767956127, 371285322017066509, 371285322255734112, 371285322257804934, 371285322139507903, 371285322021038610, 371285322010491377, 371285322062106653]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464253368779649, 362464308221654265⟩, ⟨1282085231937925129, 1284349810678772757⟩, true⟩

def words01 : List Nat := [371285322301117345, 371285322540978861, 371285322777936774, 371285322780007770, 371285322659925201, 371285322564755238, 371285322480828947, 371285322482900139, 371285322139857010, 371285321798399664]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480936021953528, 362480990893365829⟩, ⟨262409567589195599, 264675279446460745⟩, true⟩

def words02 : List Nat := [371285321456001720, 371285321382457578, 371285321187992383, 371285321188988229, 371285321189319655, 371285321141551987, 371285320837670081, 371285320671349753, 371285320602974300, 371285320605118593]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490744281704043, 362490799171994076⟩, ⟨(-337232713464462906), (-334965847515093722)⟩, true⟩

def words03 : List Nat := [371285320535868254, 371285320384946515, 371285320325782087, 371285320328068303, 371285320369089009, 371285320431348888, 371285320493711551, 371285320495833931, 371285320500044955, 371285320592194677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481767041249828, 362481821949972771⟩, ⟨211742788447760326, 214010781482476992⟩, true⟩

def words04 : List Nat := [371285320950962640, 371285321034852298, 371285321100141822, 371285321166147138, 371285321246948735, 371285321249254732, 371285321407528038, 371285321600437986, 371285321715306280, 371285321717454088]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk611A
