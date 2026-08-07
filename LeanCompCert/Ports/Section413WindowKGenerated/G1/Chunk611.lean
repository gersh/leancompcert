import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk611

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

def state06 : KState := ⟨⟨362499767896697007, 362499822824205936⟩, ⟨(-889049745428072733), (-886780603538358361)⟩, true⟩

def words05 : List Nat := [371285321872082227, 371285322085095322, 371285322564616069, 371285322688322038, 371285322761935978, 371285322836157287, 371285323097996158, 371285323227490311, 371285323465997209, 371285323705428638]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495970624695509, 362496025570894854⟩, ⟨(-656866195237823629), (-654595910144119615)⟩, true⟩

def words06 : List Nat := [371285323900279990, 371285323902353413, 371285323879784696, 371285323980890841, 371285324130018798, 371285324132133705, 371285324110870883, 371285324089528624, 371285324311212379, 371285324488516863]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484374950780583, 362484429915648019⟩, ⟨52511878618081800, 54783305733381150⟩, true⟩

def words07 : List Nat := [371285324765610389, 371285325043510511, 371285325264555328, 371285325266629041, 371285325172484841, 371285325162205087, 371285325382854414, 371285325384937875, 371285325372609951, 371285325360331468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488381582131583, 362488436565544769⟩, ⟨(-192583001986182680), (-190310440146822460)⟩, true⟩

def words08 : List Nat := [371285325582599159, 371285325729142598, 371285325980233276, 371285326232184774, 371285326442820666, 371285326444894519, 371285326299273094, 371285326264558359, 371285326407485822, 371285326460461558]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489980541765252, 362490035544120713⟩, ⟨(-290411837745236706), (-288138116737898726)⟩, true⟩

def words09 : List Nat := [371285326508943804, 371285326558121153, 371285326742757614, 371285326857328184, 371285327051281172, 371285327246003460, 371285327439319321, 371285327441394938, 371285327402326247, 371285327481887451]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk611
