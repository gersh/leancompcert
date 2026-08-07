import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk702

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552462394242466, 360552494163228577⟩, ⟨2106392902679386348, 2107899309857089588⟩, true⟩

def state01 : KState := ⟨⟨360573010959585214, 360573042737946825⟩, ⟨663739617450878615, 665246682835862647⟩, true⟩

def words00 : List Nat := [360582520791998856, 360582520567703563, 360582520313809749, 360582519902170824, 360582519490383403, 360582518982177393, 360582518575903876, 360582518372233031, 360582518168468828, 360582517836691105]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560050768040155, 360560082555784217⟩, ⟨1573731489988741553, 1575239214162001797⟩, true⟩

def words01 : List Nat := [360582517710744748, 360582517720041557, 360582517720855055, 360582517664714752, 360582517405999804, 360582516976439630, 360582516546715408, 360582516107570479, 360582515788126747, 360582515469685699]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565242887896492, 360565274685117725⟩, ⟨1208967562954097596, 1210475952660019038⟩, true⟩

def words02 : List Nat := [360582515151110640, 360582514717308999, 360582514080864082, 360582513647077704, 360582513213012416, 360582512704207110, 360582512224437540, 360582511604375745, 360582510984141132, 360582510566545321]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539477853170355, 360539509659770884⟩, ⟨3018521435927011849, 3020030484388667871⟩, true⟩

def words03 : List Nat := [360582510321946919, 360582510031864311, 360582509741682045, 360582509321765566, 360582508699279403, 360582507943198270, 360582507186836581, 360582506632969268, 360582506149072302, 360582505537965484]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587647826662396, 360587679642652455⟩, ⟨(-365185023230265303), (-363675315201960905)⟩, true⟩

def words04 : List Nat := [360582504926650705, 360582504517897716, 360582504237325096, 360582504046224758, 360582503855074652, 360582503463641510, 360582503112239422, 360582502930819797, 360582502768806854, 360582502843529283]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360569907606569600, 360569939432047027⟩, ⟨881220119314123078, 882730493877826946⟩, true⟩

def words05 : List Nat := [360582502844416108, 360582502817920747, 360582502922291200, 360582503156886585, 360582503340273705, 360582503523817858, 360582503552575607, 360582503553570899, 360582503379927267, 360582503202241702]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565125782804133, 360565157617657995⟩, ⟨1217197431057891609, 1218708464456096425⟩, true⟩

def words06 : List Nat := [360582503024232989, 360582502915761724, 360582502769662962, 360582502490083162, 360582502210354600, 360582501766621725, 360582501483573021, 360582501311684552, 360582501139686147, 360582500843279969]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580555677257710, 360580587521524169⟩, ⟨132849564094188023, 134361258961596665⟩, true⟩

def words07 : List Nat := [360582500597280071, 360582500553641353, 360582500509715469, 360582500461651113, 360582500297469824, 360582499959469301, 360582499621288507, 360582499405418703, 360582499347037811, 360582499320883327]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570278815415339, 360570310669166558⟩, ⟨855004862579135680, 856517224081353330⟩, true⟩

def words08 : List Nat := [360582499294579407, 360582499140048870, 360582498783160664, 360582498571218093, 360582498359017777, 360582498096194282, 360582497676225881, 360582497099107858, 360582496521814232, 360582496146817453]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551207841750838, 360551239704873427⟩, ⟨2195647503211980443, 2197160523474873413⟩, true⟩

def words09 : List Nat := [360582495974268880, 360582495861474429, 360582495748574797, 360582495534743508, 360582495326299178, 360582494996917344, 360582494667251709, 360582494539672138, 360582494209926589, 360582493766373781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk702
