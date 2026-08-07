import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk024

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362993639764978889, 362993639827825145⟩, ⟨(-1264120136103536840), (-1264120033730779670)⟩, true⟩

def state01 : KState := ⟨⟨362402629557574439, 362402629620968461⟩, ⟨157460791972757036, 157460895663025638⟩, true⟩

def words00 : List Nat := [371267433959871212, 371267495726916455, 371267553299876100, 371267610824977479, 371267683950598067, 371267683950665615, 371267779800127712, 371267886451926833, 371267966092134237, 371267966092197933]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨363104047747165219, 363104047811117413⟩, ⟨(-1536054315420301596), (-1536054210381998942)⟩, true⟩

def words01 : List Nat := [371268083781403753, 371268228449958248, 371268486990269777, 371268584337401757, 371268630418685929, 371268676461858037, 371268893502161822, 371269052271368762, 371269314666262242, 371269576844416877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362769592457027937, 362769592521540892⟩, ⟨(-724690662156466190), (-724690555758218708)⟩, true⟩

def words02 : List Nat := [371269837147224442, 371269963538575140, 371270260038918839, 371270556294758138, 371270887597019546, 371270993612915686, 371271096812038152, 371271199926208183, 371271365955313953, 371271488631883049]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362407254441303724, 362407254506378821⟩, ⟨157667414877444992, 157667522644577464⟩, true⟩

def words03 : List Nat := [371271635046876526, 371271781341537660, 371271925223105995, 371271925223168277, 371271845593975068, 371271815854011331, 371271924333185874, 371271924333248432, 371271898837035956, 371271872343528238]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362758548829348383, 362758548894986049⟩, ⟨(-700366578365938686), (-700366469223304088)⟩, true⟩

def words04 : List Nat := [371271986981694298, 371272070456567047, 371272217012984811, 371272363449544205, 371272479418437436, 371272479418500220, 371272435361101677, 371272496670428840, 371272685029930899, 371272801661520809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362648168501527700, 362648168567737401⟩, ⟨(-429173128629331837), (-429173018082225983)⟩, true⟩

def words05 : List Nat := [371272910969117604, 371273020187613104, 371273202538768865, 371273304394426445, 371273455244644165, 371273605972093957, 371273731081934028, 371273731081997053, 371273707991204310, 371273778881397610]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362429193670332472, 362429193737105999⟩, ⟨110139912500508309, 110140024437545737⟩, true⟩

def words06 : List Nat := [371273956793070607, 371273956793133794, 371273916219908617, 371273873148137555, 371273830111287156, 371273787194859809, 371273705185820983, 371273746078895087, 371273784840051244, 371273784840117152]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362854087322347860, 362854087389696404⟩, ⟨(-942014878830015062), (-942014765469754960)⟩, true⟩

def words07 : List Nat := [371273811658964971, 371273856487333452, 371274064100734844, 371274064100798348, 371274055283442320, 371273997229441590, 371274043601837806, 371274089501129954, 371274242726128460, 371274395827636850]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362584379931354405, 362584379999278760⟩, ⟨(-272694194389196061), (-272694079597943427)⟩, true⟩

def words08 : List Nat := [371274547442535568, 371274548809800271, 371274652569713692, 371274756246150474, 371274863514220000, 371274863514284315, 371274837060421351, 371274809561048460, 371274864304588402, 371274908269211340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362144325621181256, 362144325689684416⟩, ⟨827721983514374694, 827722099749766668⟩, true⟩

def words09 : List Nat := [371275069983956669, 371275231568993137, 371275392203790811, 371275398190268067, 371275452444767794, 371275506655844092, 371275632724706567, 371275632724770902, 371275547018044251, 371275414529584323]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk024
