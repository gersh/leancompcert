import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493945922962150, 362493998523748893⟩, ⟨(-532239164156501306), (-530110864369449618)⟩, true⟩

def state01 : KState := ⟨⟨362492210762339005, 362492263381427928⟩, ⟨(-428363218044788279), (-426233821867561147)⟩, true⟩

def words00 : List Nat := [371285148868245621, 371285148870272974, 371285148681760260, 371285148698554270, 371285148798100477, 371285148800176784, 371285148743750411, 371285148682395692, 371285148810231436, 371285148931295773]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470731247675575, 362470783885054293⟩, ⟨858674702471843583, 860805194484987719⟩, true⟩

def words01 : List Nat := [371285149303477573, 371285149676489312, 371285149997569760, 371285150018803398, 371285150074403380, 371285150130979343, 371285150265271660, 371285150267299354, 371285150030250225, 371285149792839423]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488943091309325, 362488995746830903⟩, ⟨(-232628820145719252), (-230497240920403342)⟩, true⟩

def words02 : List Nat := [371285149593723721, 371285149595978833, 371285149629859312, 371285149764255202, 371285149827563509, 371285149829595900, 371285149625373106, 371285149537425065, 371285149636914175, 371285149703198720]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493120221748925, 362493172895733780⟩, ⟨(-482942893740898716), (-480810207918087012)⟩, true⟩

def words03 : List Nat := [371285149769664815, 371285149836780607, 371285150149040543, 371285150359344945, 371285150652571912, 371285150946593974, 371285151238741834, 371285151240772975, 371285151368227791, 371285151504567165]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490098390899446, 362490151082972630⟩, ⟨(-301808597388765705), (-299674827258899767)⟩, true⟩

def words04 : List Nat := [371285151753240326, 371285151777513432, 371285151779724469, 371285151782629575, 371285151850536117, 371285151852771631, 371285151970447750, 371285152152571623, 371285152334779960, 371285152420277114]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516913470607810, 362516966181020268⟩, ⟨(-1909480337652997643), (-1907345467988780917)⟩, true⟩

def words05 : List Nat := [371285152783695740, 371285153148180422, 371285153757161128, 371285154054312511, 371285154273105999, 371285154492488309, 371285154989656149, 371285155348810016, 371285155880724498, 371285156413538259]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494665940774426, 362494718669509281⟩, ⟨(-575410955630421761), (-573274987260346221)⟩, true⟩

def words06 : List Nat := [371285156880031575, 371285157116976199, 371285157586376230, 371285158056794580, 371285158589818791, 371285158752600911, 371285158912199207, 371285159072490411, 371285159304392387, 371285159466106631]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486890570633249, 362486943317625592⟩, ⟨(-108997164926968476), (-106860101565472890)⟩, true⟩

def words07 : List Nat := [371285159905353514, 371285160345410068, 371285160783739168, 371285160883056784, 371285161067528704, 371285161253086822, 371285161655857309, 371285161688585954, 371285161719807052, 371285161751770314]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495549759395956, 362495602524577198⟩, ⟨(-628407701432028655), (-626269547007689931)⟩, true⟩

def words08 : List Nat := [371285162061218012, 371285162267043338, 371285162438797362, 371285162611363821, 371285162757158397, 371285162759188768, 371285162612903204, 371285162661338803, 371285162956728038, 371285163132884983]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496051130465483, 362496103914161724⟩, ⟨(-658473698172781565), (-656334432942814035)⟩, true⟩

def words09 : List Nat := [371285163307461548, 371285163482735529, 371285163830814919, 371285164081287564, 371285164375626329, 371285164670707664, 371285164914536296, 371285164916567033, 371285165004398056, 371285165189258093]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599
