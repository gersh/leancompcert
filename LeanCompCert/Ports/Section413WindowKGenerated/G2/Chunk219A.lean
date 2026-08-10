import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk219A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360627890479328898, 360627893285606087⟩, ⟨(-1048632274630007035), (-1048590691149062347)⟩, true⟩

def state01 : KState := ⟨⟨360588434935113888, 360588437744058122⟩, ⟨(-184610886654910755), (-184569244752209143)⟩, true⟩

def words00 : List Nat := [360580017007247512, 360580018125693688, 360580018125950003, 360580017560042579, 360580016994141763, 360580015213875633, 360580014669328668, 360580014841126891, 360580014841379001, 360580014155689166]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598720141360866, 360598722952975122⟩, ⟨(-409982975342492660), (-409941274926212968)⟩, true⟩

def words01 : List Nat := [360580016617247452, 360580019078665578, 360580022212992793, 360580023274401586, 360580023274664786, 360580022569206017, 360580021863761769, 360580020475118163, 360580021252183774, 360580022105617510]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589642920289827, 360589645734599776⟩, ⟨(-211472092045921879), (-211430332527022731)⟩, true⟩

def words02 : List Nat := [360580022105869728, 360580021912763133, 360580020397036457, 360580019166878428, 360580017936749586, 360580016143325296, 360580013519815084, 360580009851394288, 360580006183254060, 360580005028178408]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536561309895699, 360536564126875352⟩, ⟨952757802451056287, 952799620530312267⟩, true⟩

def words03 : List Nat := [360580005028412611, 360580004548797226, 360580004069196914, 360580002550598682, 360580000760417451, 360579997920325907, 360579995080410730, 360579994312820324, 360579993618378956, 360579991639205813]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605513072269941, 360605515891926462⟩, ⟨(-560275541730032951), (-560233664907652391)⟩, true⟩

def words04 : List Nat := [360579989660149369, 360579989331625778, 360579991938581154, 360579994545354363, 360579995152003249, 360579995152286917, 360579993693181978, 360579992908226408, 360579992717832756, 360579993880860559]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk219A
