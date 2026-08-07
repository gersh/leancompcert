import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk449

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490853366623208, 362490882243605118⟩, ⟨(-240827317433501169), (-239951282473836877)⟩, true⟩

def state01 : KState := ⟨⟨362485490070353616, 362485518960735999⟩, ⟨(-20318593345270), 856318117446392⟩, true⟩

def words00 : List Nat := [371285538359038247, 371285538360541137, 371285538455390952, 371285538724715857, 371285539014177241, 371285539015663169, 371285538644424199, 371285538273979793, 371285538026452312, 371285538028162351]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474492631336128, 362474521535132112⟩, ⟨494019061312570685, 494896300496720891⟩, true⟩

def words01 : List Nat := [371285538444318831, 371285538861532263, 371285539177324119, 371285539178814258, 371285538990463134, 371285538902858155, 371285539220509339, 371285539221996462, 371285539060565128, 371285538816977543]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504919766577792, 362504948683687732⟩, ⟨(-872883860360871506), (-872006023047641580)⟩, true⟩

def words02 : List Nat := [371285538694684441, 371285538696321930, 371285538881033656, 371285539191635808, 371285539412762767, 371285539414275090, 371285539526974521, 371285539832220835, 371285540580144824, 371285541013637041]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491700156859334, 362491729087504297⟩, ⟨(-278866459410908818), (-277988013900402950)⟩, true⟩

def words03 : List Nat := [371285541384864148, 371285541756560033, 371285542316162823, 371285542629260561, 371285542934368956, 371285543240036357, 371285543543685294, 371285543545172275, 371285543326549975, 371285543466047267]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477255439062165, 362477284382953558⟩, ⟨370371458482120860, 371250499355295668⟩, true⟩

def words04 : List Nat := [371285543927929858, 371285543929419227, 371285543860922076, 371285543771890026, 371285543682273783, 371285543672946776, 371285543516941762, 371285543543454963, 371285543569381978, 371285543570925868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362522567156473718, 362522596113821568⟩, ⟨(-1666578232235036872), (-1665698586426594342)⟩, true⟩

def words05 : List Nat := [371285543635171577, 371285543883926240, 371285544626483067, 371285545144605562, 371285545545818976, 371285545947451096, 371285546499757121, 371285546830966377, 371285547656025864, 371285548481730943]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494355581679287, 362494384552464329⟩, ⟨(-398130360170964027), (-397250110157579309)⟩, true⟩

def words06 : List Nat := [371285549208196231, 371285549275859334, 371285549837469681, 371285550399824994, 371285550933635549, 371285550935123368, 371285550809955122, 371285550684435221, 371285550881429137, 371285551079556065]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475378392786518, 362475407376946806⟩, ⟨455495524531146396, 456376376098459504⟩, true⟩

def words07 : List Nat := [371285551771231640, 371285552463467511, 371285553135676172, 371285553220094923, 371285553320120411, 371285553420876317, 371285553900160072, 371285553901648846, 371285553807529947, 371285553583618626]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502306384596006, 362502335382092360⟩, ⟨(-755777209097263774), (-754895757606499256)⟩, true⟩

def words08 : List Nat := [371285553541800332, 371285553571624569, 371285554094741632, 371285554618453181, 371285555064052006, 371285555065540692, 371285555276983550, 371285555630922283, 371285556190552043, 371285556565048807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498967557737885, 362498996568821836⟩, ⟨(-605503308659856654), (-604621245796519142)⟩, true⟩

def words09 : List Nat := [371285556937762391, 371285557310976506, 371285558005908261, 371285558455118237, 371285559053405136, 371285559652249139, 371285560247361751, 371285560248850903, 371285560539261345, 371285560839709227]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk449
