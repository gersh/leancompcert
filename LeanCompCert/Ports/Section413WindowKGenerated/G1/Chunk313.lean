import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk313

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362434528167253550, 362434541790736196⟩, ⟨1591217078824611544, 1591505303034933214⟩, true⟩

def state01 : KState := ⟨⟨362482364037125752, 362482377669620848⟩, ⟨93775897213663829, 94064403559517275⟩, true⟩

def words00 : List Nat := [371285386981766399, 371285386298085072, 371285385196969103, 371285384814173634, 371285384431056332, 371285383879446293, 371285382413468478, 371285381965615790, 371285381961249531, 371285381962292823]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502619446161190, 362502633087868279⟩, ⟨(-540545485761031310), (-540256690942733926)⟩, true⟩

def words01 : List Nat := [371285381867116684, 371285381551902006, 371285381838608376, 371285382032687992, 371285382538473849, 371285383044603433, 371285383424872539, 371285383425897649, 371285383511536670, 371285384063541383]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495740274637567, 362495753925317142⟩, ⟨(-325026085902007517), (-324737010019347993)⟩, true⟩

def words02 : List Nat := [371285385631416947, 371285385842850647, 371285386063299035, 371285386284064025, 371285386542817521, 371285386543929324, 371285387237799278, 371285388093527701, 371285388874475825, 371285389206348091]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507018538354677, 362507032198143004⟩, ⟨(-678388718948091937), (-678099357640650303)⟩, true⟩

def words03 : List Nat := [371285389864191988, 371285390522521085, 371285392196118324, 371285392514149190, 371285392663721048, 371285392813605630, 371285393978706204, 371285394640632947, 371285395331747892, 371285396023239822]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477471239697952, 362477484908589722⟩, ⟨247679057626532914, 247968704281772530⟩, true⟩

def words04 : List Nat := [371285396708912135, 371285396709920698, 371285396048977996, 371285396058885312, 371285396380114037, 371285396381140057, 371285395858848497, 371285395304593031, 371285394749971613, 371285394596126621]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461702418429624, 362461716096422908⟩, ⟨742239002545384621, 742528934578643305⟩, true⟩

def words05 : List Nat := [371285395016716778, 371285395689976809, 371285396157513098, 371285396158522163, 371285395428246222, 371285395010497886, 371285395187708303, 371285395188717256, 371285394431126560, 371285393677244932]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362443341478946077, 362443355165957602⟩, ⟨1318269151844114219, 1318559366736824607⟩, true⟩

def words06 : List Nat := [371285392922933736, 371285392700634442, 371285392124512723, 371285392281091294, 371285392281882038, 371285392102953014, 371285390570761762, 371285389461830349, 371285388352444306, 371285387660912554]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466359015295982, 362466372711493022⟩, ⟨596112775853816308, 596403278942180564⟩, true⟩

def words07 : List Nat := [371285386321815539, 371285384986440552, 371285383650740616, 371285383179243735, 371285382362109559, 371285381831802752, 371285381301175981, 371285380774375506, 371285379156571073, 371285378552122155]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462272043746310, 362462285748945481⟩, ⟨724392376637004253, 724683162259185819⟩, true⟩

def words08 : List Nat := [371285377947171360, 371285377765265829, 371285376905982072, 371285375864849761, 371285374823389088, 371285374094144999, 371285372856025627, 371285372630540415, 371285372404717223, 371285372182913598]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362526179698415102, 362526193412755478⟩, ⟨(-1281922580163932893), (-1281631507553960463)⟩, true⟩

def words09 : List Nat := [371285371724607791, 371285372002279655, 371285373291178627, 371285373670295765, 371285373829039749, 371285373988060719, 371285375158340458, 371285375820950003, 371285377121561137, 371285378422546442]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk313
