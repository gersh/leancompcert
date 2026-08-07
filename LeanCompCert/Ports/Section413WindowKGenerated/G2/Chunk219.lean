import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk219

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

def state06 : KState := ⟨⟨360540308708277454, 360540311530640720⟩, ⟨871462154005534203, 871504090254439159⟩, true⟩

def words05 : List Nat := [360579993960854006, 360579994040873500, 360579995197249717, 360579997395463247, 360579999064363824, 360580000733160439, 360580001056312264, 360580001056596072, 360579999316199844, 360579997509249757]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360551184650399673, 360551187475436080⟩, ⟨632539302918391051, 632581297882929977⟩, true⟩

def words06 : List Nat := [360579995962587738, 360579995962871620, 360579994876113445, 360579992746424753, 360579990616882828, 360579987327219627, 360579985648183069, 360579984254413908, 360579982860742950, 360579980433919600]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596359133321559, 360596361961041276⟩, ⟨(-360428446904204499), (-360386392974269853)⟩, true⟩

def words07 : List Nat := [360579979309556087, 360579979495756678, 360579979495990563, 360579978986367557, 360579976416020127, 360579972111848721, 360579967808014727, 360579965568815931, 360579965855511562, 360579966601732134]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360484204774410135, 360484207604833963⟩, ⟨2104968789909274746, 2105010903289302236⟩, true⟩

def words08 : List Nat := [360579966601985876, 360579965886445583, 360579964153459592, 360579961980149300, 360579959806961951, 360579957106955305, 360579952348656335, 360579945946496040, 360579939544865023, 360579933430358716]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360496604858999930, 360496607692100831⟩, ⟨1832410012898001262, 1832452185160334236⟩, true⟩

def words09 : List Nat := [360579929077634127, 360579926786861963, 360579924496267126, 360579921165691943, 360579917908086199, 360579913753546140, 360579909599296651, 360579907506056631, 360579904759178391, 360579900973244483]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk219
