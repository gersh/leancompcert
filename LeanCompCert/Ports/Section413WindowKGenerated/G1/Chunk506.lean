import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk506

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362531516437979114, 362531553469672119⟩, ⟨(-2354261652124693760), (-2352995730431974532)⟩, true⟩

def state01 : KState := ⟨⟨362491339515610804, 362491376562550966⟩, ⟨(-321159394199040296), (-319892700920209350)⟩, true⟩

def words00 : List Nat := [371285053383380905, 371285053750174830, 371285054278669620, 371285054807979448, 371285055398885905, 371285055470133539, 371285055539132181, 371285055608707828, 371285055819612006, 371285055946461180]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362457297718463430, 362457334780584896⟩, ⟨1401933149615842000, 1403200611298532822⟩, true⟩

def words01 : List Nat := [371285056205356621, 371285056464904701, 371285056723967662, 371285056725657806, 371285056464651464, 371285056300395466, 371285056135252633, 371285056131330320, 371285055607073395, 371285055061329632]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483092520494585, 362483129597757909⟩, ⟨96101789952335798, 97370018191356520⟩, true⟩

def words02 : List Nat := [371285054514872636, 371285054293180644, 371285053976063722, 371285053857379343, 371285053738133168, 371285053557330246, 371285052976257196, 371285052785894562, 371285052764448688, 371285052766199374]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483680239034536, 362483717331738894⟩, ⟨66318125506669610, 67587135604092026⟩, true⟩

def words03 : List Nat := [371285052729501991, 371285052618741431, 371285052594604846, 371285052596487079, 371285052531415178, 371285052483602038, 371285052435236352, 371285052387344945, 371285052015053928, 371285051990814805]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471407119276179, 362471444227032582⟩, ⟨687903644693002820, 689173417105170352⟩, true⟩

def words04 : List Nat := [371285052272016535, 371285052273707846, 371285052061999540, 371285051799161467, 371285051535711115, 371285051287855910, 371285050875842969, 371285050854017582, 371285050831599499, 371285050809798726]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502024773984840, 362502061897044387⟩, ⟨(-862979459439045578), (-861708911846997718)⟩, true⟩

def words05 : List Nat := [371285050663092489, 371285050785928076, 371285051214265452, 371285051340499018, 371285051350754461, 371285051361549988, 371285051731396350, 371285051907373362, 371285052244309446, 371285052581952956]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498819603739037, 362498856742070390⟩, ⟨(-700652173647070643), (-699380852306862165)⟩, true⟩

def words06 : List Nat := [371285052916006233, 371285052917698521, 371285052954146451, 371285053120044195, 371285053404440138, 371285053504265054, 371285053603858713, 371285053704003815, 371285054078739084, 371285054353084445]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479365215892503, 362479402369499354⟩, ⟨285319289940386118, 286591385368205296⟩, true⟩

def words07 : List Nat := [371285055015648201, 371285055678895075, 371285056255483707, 371285056460430684, 371285056780629435, 371285057101631986, 371285057509187030, 371285057510879590, 371285057399917893, 371285057290284047]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489740196570825, 362489777365326230⟩, ⟨(-240466275794458033), (-239193412562261337)⟩, true⟩

def words08 : List Nat := [371285057384577703, 371285057396673074, 371285057796907040, 371285058197797364, 371285058571394132, 371285058573086945, 371285058428081873, 371285058370456083, 371285058614064878, 371285058708906703]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488525705659201, 362488562889825251⟩, ⟨(-178832456526135244), (-177558812051960712)⟩, true⟩

def words09 : List Nat := [371285058779361387, 371285058850376382, 371285059261869481, 371285059558415389, 371285059973575810, 371285060389382148, 371285060789240834, 371285060790934349, 371285060741541138, 371285060812705432]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk506
