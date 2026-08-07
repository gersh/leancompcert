import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk391

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452716164655376, 362452737818607656⟩, ⟨1267333845434439541, 1267905990568660417⟩, true⟩

def state01 : KState := ⟨⟨362466566296148456, 362466587961566084⟩, ⟨725880054819738785, 726452648306766533⟩, true⟩

def words00 : List Nat := [371285164253341483, 371285163974340474, 371285163698626407, 371285163888429574, 371285163897361428, 371285163898640831, 371285163036679672, 371285162828645654, 371285162619990136, 371285162562647822]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477782332478206, 362477804009567505⟩, ⟨287210738004359399, 287783788029198645⟩, true⟩

def words01 : List Nat := [371285162088684429, 371285161615627987, 371285161320747413, 371285161322170915, 371285161334433943, 371285161440863751, 371285161471116624, 371285161472396474, 371285160632317903, 371285160445866820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362456712925883316, 362456734614384609⟩, ⟨1111524052430294841, 1112097548950995841⟩, true⟩

def words02 : List Nat := [371285160383788697, 371285160385069636, 371285159779968416, 371285159032866262, 371285158285325567, 371285157730199094, 371285156847827514, 371285156298813706, 371285155749384674, 371285155200864318]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502113926286311, 362502135626341946⟩, ⟨(-665224135658295162), (-664650186956827730)⟩, true⟩

def words03 : List Nat := [371285154475440027, 371285154337689755, 371285154712429354, 371285154713713284, 371285154561994377, 371285154303357283, 371285154053351591, 371285154054771624, 371285154271132568, 371285154706412542]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476938449751762, 362476960161370290⟩, ⟨320196669783331868, 320771071114590908⟩, true⟩

def words04 : List Nat := [371285155141182047, 371285155142462889, 371285154707927269, 371285154705993503, 371285154898251787, 371285154899535183, 371285154477662425, 371285154056747397, 371285153635351018, 371285153547605657]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452727005329977, 362452748728509505⟩, ⟨1268194806176474408, 1268769660179575144⟩, true⟩

def words05 : List Nat := [371285153339216454, 371285153215348086, 371285153091038174, 371285152970088309, 371285151980166916, 371285151091983136, 371285150203188986, 371285149966443527, 371285149188250564, 371285148362324101]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467126915454362, 362467148650095914⟩, ⟨704373409240787487, 704948712153598927⟩, true⟩

def words06 : List Nat := [371285147535849274, 371285147361447854, 371285147082381066, 371285147269513743, 371285147289749549, 371285147291031111, 371285146442989715, 371285146147837416, 371285145852005402, 371285145808945891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362457756399568581, 362457778145875210⟩, ⟨1071527253863945144, 1072103013758442446⟩, true⟩

def words07 : List Nat := [371285145350459571, 371285144769209789, 371285144187457157, 371285144139519243, 371285143765125287, 371285143587210663, 371285143408870921, 371285143224357580, 371285142370387298, 371285141673536222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464140696921313, 362464162454652990⟩, ⟨821455989882822871, 822032197469304335⟩, true⟩

def words08 : List Nat := [371285140976018648, 371285140929868929, 371285140499413813, 371285139997922575, 371285139495951125, 371285139053120615, 371285138374070313, 371285138254310432, 371285138134135566, 371285138014680276]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488744934975914, 362488766704329306⟩, ⟨(-142940505558785065), (-142363842461426329)⟩, true⟩

def words09 : List Nat := [371285137595749294, 371285137712703096, 371285137907425907, 371285137908708469, 371285137236571991, 371285136479053207, 371285135721064843, 371285135436351952, 371285134972168064, 371285135066298097]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk391
