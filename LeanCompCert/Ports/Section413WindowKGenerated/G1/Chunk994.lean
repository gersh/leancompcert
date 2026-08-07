import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484512778282952, 362484663435668360⟩, ⟨58769349945248167, 68879815115385063⟩, true⟩

def state01 : KState := ⟨⟨362490832611054384, 362490983299674498⟩, ⟨(-569413224367978431), (-559299654306260519)⟩, true⟩

def words00 : List Nat := [371285356481229933, 371285356528804503, 371285356665388920, 371285356803362115, 371285356923640996, 371285356935338207, 371285356957557710, 371285356981589270, 371285357104986099, 371285357165199377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496754360174237, 362496905080596931⟩, ⟨(-1158117705530704463), (-1148000973813718823)⟩, true⟩

def words01 : List Nat := [371285357223515082, 371285357282969873, 371285357431505637, 371285357545430869, 371285357673784625, 371285357803518178, 371285357934423175, 371285357975554905, 371285358094070387, 371285358214504117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483169819220094, 362483320570815004⟩, ⟨192525215062414816, 202645046079669308⟩, true⟩

def words02 : List Nat := [371285358374624454, 371285358400973138, 371285358426415765, 371285358453082524, 371285358484827258, 371285358488679919, 371285358534446647, 371285358597151704, 371285358634640552, 371285358638260239]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496489838682904, 362496640621896341⟩, ⟨(-1131951722236483658), (-1121828747229302114)⟩, true⟩

def words03 : List Nat := [371285358700825543, 371285358785771410, 371285358932807808, 371285358958753420, 371285358961505391, 371285358961182419, 371285359022272143, 371285359038403562, 371285359154224818, 371285359271676319]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491600932660261, 362491751747462007⟩, ⟨(-645785600570410809), (-635659484263630213)⟩, true⟩

def words04 : List Nat := [371285359378451105, 371285359402140889, 371285359518097726, 371285359635828510, 371285359782369575, 371285359825313440, 371285359867258836, 371285359910419261, 371285359993935733, 371285360062267654]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482171420721715, 362482322266956900⟩, ⟨292052881086307218, 302182123605199040⟩, true⟩

def words05 : List Nat := [371285360180749097, 371285360300610944, 371285360419216049, 371285360422712276, 371285360418151016, 371285360434214021, 371285360541079971, 371285360544576300, 371285360521274363, 371285360494622346]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490391451648252, 362490542329218703⟩, ⟨(-525549425901336716), (-515417066619489732)⟩, true⟩

def words06 : List Nat := [371285360526687812, 371285360556017644, 371285360609578991, 371285360664541423, 371285360705571190, 371285360709069233, 371285360631741087, 371285360620200300, 371285360692208213, 371285360747987797]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484845776050390, 362484996685478441⟩, ⟨26119397252349313, 36254925574051737⟩, true⟩

def words07 : List Nat := [371285360801380312, 371285360855999149, 371285360960982963, 371285361021365392, 371285361090655945, 371285361161265250, 371285361210955118, 371285361214451978, 371285361129142958, 371285361129844888]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480987948969045, 362481138889561674⟩, ⟨409923780655032784, 420062409389905668⟩, true⟩

def words08 : List Nat := [371285361211588598, 371285361215085537, 371285361166059792, 371285361118225020, 371285361068971922, 371285361044974375, 371285360991860009, 371285361018490778, 371285361043036002, 371285361046656758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487782421520037, 362487933393700040⟩, ⟨(-266115387118716631), (-255973615596317999)⟩, true⟩

def words09 : List Nat := [371285361006632335, 371285360998416639, 371285361054572192, 371285361058069661, 371285360992325334, 371285360893346946, 371285360792914768, 371285360795080433, 371285360790646312, 371285360820403327]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994
