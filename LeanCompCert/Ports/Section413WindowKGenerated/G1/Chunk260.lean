import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk260

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362510890991332179, 362510900246336736⟩, ⟨(-659648136195365271), (-659485456352882191)⟩, true⟩

def state01 : KState := ⟨⟨362471347220889826, 362471356483321227⟩, ⟨368573705388538685, 368736578367227921⟩, true⟩

def words00 : List Nat := [371285537345665307, 371285537346488740, 371285536781509579, 371285537238616739, 371285537767860440, 371285537768684057, 371285536328345714, 371285534880442539, 371285533432310373, 371285533206826311]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362413904407035954, 362413913676887836⟩, ⟨1863086202067635382, 1863249268091166274⟩, true⟩

def words01 : List Nat := [371285532944251466, 371285533227022894, 371285533299000786, 371285533299824623, 371285531403580911, 371285529501208562, 371285527598545771, 371285527172260896, 371285524778169004, 371285522026929772]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488291445422036, 362488300722650481⟩, ⟨(-72770831768268362), (-72607573768689496)⟩, true⟩

def words02 : List Nat := [371285519275544954, 371285518000270987, 371285515992439177, 371285515239081125, 371285514485519064, 371285513456890663, 371285511867801479, 371285511201195015, 371285511341320662, 371285511449331412]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362463988024229069, 362463997308983887⟩, ⟨560024977431391206, 560188431380036140⟩, true⟩

def words03 : List Nat := [371285511549706082, 371285511650360726, 371285512361993470, 371285512362901328, 371285512509590027, 371285512677527459, 371285512678154283, 371285512535449711, 371285510746679591, 371285509921556086]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362441610577100682, 362441619869199301⟩, ⟨1142992280560387308, 1143155925779749512⟩, true⟩

def words04 : List Nat := [371285509743193277, 371285509744018544, 371285508814875968, 371285507878929466, 371285506942745379, 371285506453004498, 371285505223389345, 371285504495793311, 371285503767959169, 371285503014142862]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501768025425170, 362501777324965234⟩, ⟨(-424280481908662350), (-424116642801221554)⟩, true⟩

def words05 : List Nat := [371285501330194183, 371285500947676148, 371285501653168962, 371285501654008008, 371285501523719801, 371285501206897650, 371285501818155731, 371285502077202137, 371285502702297053, 371285503327697239]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464339967292287, 362464349274294647⟩, ⟨551102871318232323, 551266904930130539⟩, true⟩

def words06 : List Nat := [371285503552304056, 371285503553129450, 371285502047440212, 371285501770774692, 371285501493706753, 371285501480469516, 371285499506801700, 371285497527168723, 371285495547343320, 371285494916984718]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362445606735213357, 362445616049650370⟩, ⟨1039628160584683778, 1039792388055915026⟩, true⟩

def words07 : List Nat := [371285494218988584, 371285494332403708, 371285494458298127, 371285494459123894, 371285492626085659, 371285490797826151, 371285488969289205, 371285488439612986, 371285486917535269, 371285485389683189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362450325459272788, 362450334781110696⟩, ⟨916712659314988942, 916877079839506260⟩, true⟩

def words08 : List Nat := [371285483861574390, 371285483083495335, 371285482079990846, 371285482312818307, 371285482313458606, 371285482184783420, 371285480098934404, 371285479074660615, 371285478050041670, 371285477635838159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362449510373523232, 362449519702891138⟩, ⟨938014706783713797, 938179323803594999⟩, true⟩

def words09 : List Nat := [371285476289531229, 371285474842281443, 371285473394809412, 371285473133554642, 371285472142146156, 371285471259910493, 371285470377438461, 371285469489827116, 371285466647106120, 371285465270852962]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk260
