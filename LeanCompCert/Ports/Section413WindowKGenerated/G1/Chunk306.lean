import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk306

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467351713103915, 362467364709352606⟩, ⟨557339269999559192, 557608080342193832⟩, true⟩

def state01 : KState := ⟨⟨362475137191577734, 362475150196580264⟩, ⟨319183344006538265, 319452422262862829⟩, true⟩

def words00 : List Nat := [371285586920251953, 371285586921246089, 371285586625352521, 371285586273082293, 371285585920450584, 371285585893535318, 371285585698595804, 371285586067143168, 371285586406678985, 371285586407696333]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488808742161840, 362488821756050348⟩, ⟨(-99455570174512345), (-99186219873103523)⟩, true⟩

def words01 : List Nat := [371285586172444819, 371285586278601794, 371285586727904110, 371285586728887342, 371285585758684285, 371285584674685313, 371285583590351235, 371285583183115444, 371285582492386404, 371285582599266667]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454681954360661, 362454694977121858⟩, ⟨945580358183897694, 945849980210700748⟩, true⟩

def words02 : List Nat := [371285582613470687, 371285582614454395, 371285581373050564, 371285581106914930, 371285580840302383, 371285580626689231, 371285578994522098, 371285577284194417, 371285575573580479, 371285574832825766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362440139717343314, 362440152748983068⟩, ⟨1391274064034192703, 1391543958056444321⟩, true⟩

def words03 : List Nat := [371285573879667417, 371285573935055851, 371285573994170604, 371285573995157372, 371285573071785103, 371285572166281980, 371285571415775117, 371285571416759089, 371285570155680914, 371285568674507104]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489446824690003, 362489459865133400⟩, ⟨(-119698519941804508), (-119428356129930652)⟩, true⟩

def words04 : List Nat := [371285567192983973, 371285566416879578, 371285565106238916, 371285564857708173, 371285564608904456, 371285564131237675, 371285563077514171, 371285562813005166, 371285563343522084, 371285563471667284]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362454275912907537, 362454288962326609⟩, ⟨958527991605035036, 958798430565913242⟩, true⟩

def words05 : List Nat := [371285563472405664, 371285563445928759, 371285563590361677, 371285563591461080, 371285563481580848, 371285563589767152, 371285563590508639, 371285563475945420, 371285561945558970, 371285560926793860]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362427503493832660, 362427516552015067⟩, ⟨1779604515638379803, 1779875223329283411⟩, true⟩

def words06 : List Nat := [371285559948213871, 371285559949198719, 371285558575381712, 371285557192011162, 371285555808346154, 371285554750009700, 371285553302201485, 371285552084893403, 371285550867331616, 371285549653525641]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486542800817865, 362486555867915809⟩, ⟨(-31356368537663569), (-31085387363189605)⟩, true⟩

def words07 : List Nat := [371285547762078269, 371285546931109661, 371285546099661656, 371285546089272105, 371285545215654646, 371285544170369300, 371285543137961350, 371285543139046505, 371285542653387230, 371285542687531755]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471677624732106, 362471690700742657⟩, ⟨424653913390385477, 424925168047995871⟩, true⟩

def words08 : List Nat := [371285542688288513, 371285542528993547, 371285541434435003, 371285541239087962, 371285541043282171, 371285540906332812, 371285539523535926, 371285538136659367, 371285536749441148, 371285536421435000]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362449307767159966, 362449320852017615⟩, ⟨1111433544979070160, 1111705071200857360⟩, true⟩

def words09 : List Nat := [371285536418168170, 371285536866395889, 371285537296893519, 371285537297879315, 371285536448094990, 371285535640692731, 371285535082583865, 371285535083569687, 371285533922067861, 371285532743587676]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk306
