import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575A

def state06 : KState := ⟨⟨362499219732291498, 362499268150095326⟩, ⟨(-824075672644063320), (-822193074736853736)⟩, true⟩

def words05 : List Nat := [371284984636543625, 371284984463798982, 371284984369910844, 371284984371886010, 371284984203307165, 371284983984235435, 371284983845300849, 371284983847440680, 371284984043054751, 371284984293408736]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478799750670573, 362478848186032396⟩, ⟨351338625281542789, 353222233912963813⟩, true⟩

def words06 : List Nat := [371284984486916242, 371284984488863193, 371284984414336544, 371284984455927339, 371284984550733833, 371284984552675768, 371284984283984823, 371284984022010029, 371284983759192722, 371284983712068752]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464938944839460, 362464987397648604⟩, ⟨1149487492991009438, 1151372106156444376⟩, true⟩

def words07 : List Nat := [371284983802179846, 371284983999630283, 371284984198292888, 371284984200248285, 371284984129316525, 371284984070386480, 371284984097057464, 371284984098999851, 371284983784901030, 371284983439784006]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474489369926067, 362474537840144973⟩, ⟨599606017530825261, 601491633239559289⟩, true⟩

def words08 : List Nat := [371284983093834089, 371284983008412301, 371284982887430427, 371284982961466064, 371284982962979686, 371284982938230478, 371284982510815300, 371284982386161194, 371284982260552582, 371284982216481830]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486237752827748, 362486286240793263⟩, ⟨(-77019247462892664), (-75132609643370418)⟩, true⟩

def words09 : List Nat := [371284982036595438, 371284981858345858, 371284981800639636, 371284981802782439, 371284981890248588, 371284981980968494, 371284982073656490, 371284982075601134, 371284981852747902, 371284981877854367]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575B
