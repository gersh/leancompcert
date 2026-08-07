import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk084

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668925394576352, 360668925771662947⟩, ⟨(-754034368844060856), (-754032221184872586)⟩, true⟩

def state01 : KState := ⟨⟨360549648027308872, 360549648405334722⟩, ⟨248203765252248626, 248205920806029188⟩, true⟩

def words00 : List Nat := [360579189056589758, 360579193362557017, 360579193362645944, 360579190642001614, 360579187921987908, 360579178812261722, 360579176653907600, 360579173967891453, 360579171282503247, 360579161594491206]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360780492493062889, 360780492872031983⟩, ⟨(-1694881748148892752), (-1694879584657752394)⟩, true⟩

def words01 : List Nat := [360579158504982468, 360579158924282427, 360579167832895333, 360579177600173665, 360579177600267356, 360579172110471358, 360579166894612878, 360579176850389179, 360579200759736452, 360579224663427572]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360789117801481532, 360789118181404484⟩, ⟨(-1768857064152027673), (-1768854892624694669)⟩, true⟩

def words02 : List Nat := [360579237573339960, 360579237573440028, 360579249397251450, 360579262280421059, 360579270883828658, 360579277993107351, 360579277993196520, 360579277219958369, 360579289605653184, 360579314493511625]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360387093900056924, 360387094280922649⟩, ⟨1623241607987805960, 1623243787467487352⟩, true⟩

def words03 : List Nat := [360579353303905782, 360579392105114868, 360579423649993219, 360579441253253069, 360579448858776882, 360579456462522879, 360579457462177541, 360579457462277775, 360579444534103420, 360579421743892731]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618662143427694, 360618662525242095⟩, ⟨(-331869551021033971), (-331867363529840879)⟩, true⟩

def words04 : List Nat := [360579398959059664, 360579382069405742, 360579386030627520, 360579394958092902, 360579394958185313, 360579391669917778, 360579386713966227, 360579391180555757, 360579391180638719, 360579392928326956]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360468938266582627, 360468938649353619⟩, ⟨934418622497963180, 934420818077189706⟩, true⟩

def words05 : List Nat := [360579392928417294, 360579390339665090, 360579394004662267, 360579407530824136, 360579413431131252, 360579419330060792, 360579419330150338, 360579418263436310, 360579403339872840, 360579390282696077]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590985668993246, 360590986052713595⟩, ⟨(-99393561830531891), (-99391358215027881)⟩, true⟩

def words06 : List Nat := [360579378020258766, 360579378020359337, 360579364961363375, 360579340844529239, 360579316733376735, 360579289066356214, 360579271107984737, 360579266975676378, 360579262844333617, 360579252921062666]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360707815241052260, 360707815625722678⟩, ⟨(-1089634200984175118), (-1089631989316848792)⟩, true⟩

def words07 : List Nat := [360579262360832565, 360579271798403292, 360579288140237326, 360579299841518654, 360579300086136214, 360579300330704372, 360579300330787447, 360579306132752579, 360579321287255624, 360579336438207427]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360433344337761700, 360433344723392100⟩, ⟨1238274828938008886, 1238277048750804414⟩, true⟩

def words08 : List Nat := [360579340735048447, 360579340735149285, 360579331240660117, 360579326054379629, 360579320869293516, 360579312173071495, 360579289695031874, 360579257150760480, 360579224614137800, 360579195965883361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360273298122960953, 360273298509543851⟩, ⟨2597732237952150349, 2597734465856441707⟩, true⟩

def words09 : List Nat := [360579178788809287, 360579161064506568, 360579143344366293, 360579116554765576, 360579083118211794, 360579046204718040, 360579009299882864, 360578979376705048, 360578950287984253, 360578914329056374]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk084
