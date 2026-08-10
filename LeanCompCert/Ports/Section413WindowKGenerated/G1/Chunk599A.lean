import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599A
