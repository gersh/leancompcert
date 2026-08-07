import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk155

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362535069526125676, 362535072670845938⟩, ⟨(-791150724182712252), (-791117751813795398)⟩, true⟩

def state01 : KState := ⟨⟨362469366206204907, 362469369355171442⟩, ⟨227413518737258416, 227446556944820748⟩, true⟩

def words00 : List Nat := [371284039392040150, 371284039392511658, 371284040202665126, 371284042161294087, 371284044378697909, 371284044379168884, 371284041058811945, 371284037750903947, 371284034443237860, 371284033865612759]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362410776292245038, 362410779445460142⟩, ⟨1136814184939357348, 1136847289064015082⟩, true⟩

def words01 : List Nat := [371284036128418031, 371284039336439498, 371284042534432106, 371284042534903466, 371284040200920457, 371284038567545236, 371284038548387410, 371284038548858864, 371284034634631805, 371284029915116329]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451884084667074, 362451887242102129⟩, ⟨498590749784693759, 498623919424962399⟩, true⟩

def words02 : List Nat := [371284025195997194, 371284021440881230, 371284016150549236, 371284013412751285, 371284010675168786, 371284006948766577, 371283999812880191, 371283996823016804, 371283994383882089, 371283994384370318]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362438526059285873, 362438529221022404⟩, ⟨706128569107373373, 706161805571323085⟩, true⟩

def words03 : List Nat := [371283992317429729, 371283990191929080, 371283988066517812, 371283987633069297, 371283985126322712, 371283983315485181, 371283981504716400, 371283979684822844, 371283973702419733, 371283970778652477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362395887305199514, 362395890471138867⟩, ⟨1369165462420669737, 1369198764218320703⟩, true⟩

def words04 : List Nat := [371283969069304722, 371283969069778102, 371283966099925773, 371283962216305651, 371283958333000786, 371283955683249709, 371283950979585080, 371283947945906577, 371283944912460843, 371283941838612714]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362542559867236528, 362542563037452089⟩, ⟨(-912263794942521158), (-912230426628679804)⟩, true⟩

def words05 : List Nat := [371283936176830614, 371283934649239091, 371283934998680629, 371283934999164555, 371283934584720744, 371283932943780164, 371283932994102150, 371283932994622639, 371283936402815443, 371283940170886401]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499768806727541, 362499771981218839⟩, ⟨(-246467012157973093), (-246433577291743503)⟩, true⟩

def words06 : List Nat := [371283943316829022, 371283943317302372, 371283944174335395, 371283946440919014, 371283948966825396, 371283948967298765, 371283946831637855, 371283944686241195, 371283944519063467, 371283945536077760]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362441862920897281, 362441866099644274⟩, ⟨655697183006741324, 655730684155661122⟩, true⟩

def words07 : List Nat := [371283949513883979, 371283953491367406, 371283957160382859, 371283957160858457, 371283956942282952, 371283956725299708, 371283959385739419, 371283959386212896, 371283956777860424, 371283954076804458]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362441902844279202, 362441906027270061⟩, ⟨655604545135837009, 655638112426102197⟩, true⟩

def words08 : List Nat := [371283952792036961, 371283952823924759, 371283956972110219, 371283961119961394, 371283964644843831, 371283964645317498, 371283962688425135, 371283961929151510, 371283961169738042, 371283961069760511]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478930188016432, 362478933375329472⟩, ⟨78228185534553655, 78261820229192107⟩, true⟩

def words09 : List Nat := [371283958372722762, 371283955663108053, 371283953638829347, 371283953639351763, 371283953068620600, 371283953396856600, 371283953737102416, 371283953737579688, 371283950479691336, 371283950158677498]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk155
