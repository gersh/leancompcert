import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk742

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468046021725086, 362468128101491860⟩, ⟨1267266356412003273, 1271379276985483507⟩, true⟩

def state01 : KState := ⟨⟨362483945681173365, 362484027783761907⟩, ⟨87475969394242282, 91590583459533864⟩, true⟩

def words00 : List Nat := [371285262363905690, 371285262317185366, 371285262235551198, 371285262287315395, 371285262289313718, 371285262278597214, 371285262104119602, 371285262006852479, 371285261989224394, 371285261991866739]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490374989509583, 362490457115308955⟩, ⟨(-389663885554623744), (-385547548895134140)⟩, true⟩

def words01 : List Nat := [371285261977144603, 371285261948323993, 371285262040293009, 371285262119514539, 371285262253188400, 371285262387859013, 371285262490778248, 371285262493330975, 371285262453743664, 371285262526865050]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486817687300309, 362486899835868777⟩, ⟨(-125630172095731010), (-121512145397048698)⟩, true⟩

def words02 : List Nat := [371285262646556230, 371285262649117053, 371285262618951731, 371285262590492255, 371285262585677058, 371285262588489780, 371285262643639017, 371285262759451012, 371285262865069049, 371285262889776214]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496024892974765, 362496107064626609⟩, ⟨(-809087546506720459), (-804967806214619481)⟩, true⟩

def words03 : List Nat := [371285263094797360, 371285263301188017, 371285263640043034, 371285263737951163, 371285263782975379, 371285263828735477, 371285264027379053, 371285264136355957, 371285264284156131, 371285264433112828]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483515357554387, 362483597552277403⟩, ⟨119672657203343395, 123794110415389345⟩, true⟩

def words04 : List Nat := [371285264588547415, 371285264593724734, 371285264717944570, 371285264843453107, 371285265014399999, 371285265016952990, 371285264946333297, 371285264876926586, 371285264810057985, 371285264813023739]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476438779899475, 362476520997588728⟩, ⟨645197171345228250, 649320329911092034⟩, true⟩

def words05 : List Nat := [371285264908707839, 371285265027864434, 371285265145729087, 371285265148282394, 371285265043771915, 371285264996141458, 371285265077380770, 371285265079934228, 371285264989813163, 371285264874910451]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470758100069588, 362470840340625338⟩, ⟨1067079260866368229, 1071204117618088101⟩, true⟩

def words06 : List Nat := [371285264758909433, 371285264705260266, 371285264559862177, 371285264480120443, 371285264399562766, 371285264289812364, 371285263960870400, 371285263761850799, 371285263561521860, 371285263447096566]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468612037003030, 362468694300832037⟩, ⟨1226489036337701534, 1230615621712127128⟩, true⟩

def words07 : List Nat := [371285263254813968, 371285263057215465, 371285262858532413, 371285262768639337, 371285262587077463, 371285262462426402, 371285262336990812, 371285262176945496, 371285261774612809, 371285261554759234]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470326380227849, 362470408666818097⟩, ⟨1099137300566913783, 1103265576764303069⟩, true⟩

def words08 : List Nat := [371285261333456858, 371285261260870949, 371285261014285407, 371285260732350616, 371285260449419506, 371285260215812938, 371285259891007138, 371285259748267972, 371285259604636354, 371285259462036354]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498328499664703, 362498410809337409⟩, ⟨(-981309701103612398), (-977179709995333002)⟩, true⟩

def words09 : List Nat := [371285259263898867, 371285259142735129, 371285259077043422, 371285259079615586, 371285258980464873, 371285258862234821, 371285258802863397, 371285258814687896, 371285258993432691, 371285259173289505]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk742
