import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk089

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362586038280229249, 362586039266391937⟩, ⟨(-924453261902042556), (-924447318919340996)⟩, true⟩

def state01 : KState := ⟨⟨362469111871557032, 362469112860050245⟩, ⟨116312559446122692, 116318523182011500⟩, true⟩

def words00 : List Nat := [371282190976733436, 371282190976991351, 371282187539172014, 371282190333479733, 371282194930742342, 371282194931000447, 371282185688697252, 371282176516583824, 371282167688391672, 371282167688690202]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362392397783674198, 362392398774495370⟩, ⟨800198618227072613, 800204602717155209⟩, true⟩

def words01 : List Nat := [371282167232176830, 371282168240564927, 371282169325380547, 371282169325638784, 371282153702625572, 371282141930409633, 371282130160704797, 371282127757139452, 371282117868577187, 371282107810674424]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478962536195142, 362478963529329871⟩, ⟨27621903513788038, 27627908652265622⟩, true⟩

def words02 : List Nat := [371282097754912003, 371282093983407452, 371282086337361512, 371282088763072881, 371282088763277231, 371282086749816295, 371282068077259630, 371282060344092083, 371282057359817943, 371282057360086004]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483522333341810, 362483523328832938⟩, ⟨(-12790077538837049), (-12784051345524231)⟩, true⟩

def words03 : List Nat := [371282057013865857, 371282055947758375, 371282066285315373, 371282071410253286, 371282080376670248, 371282089341181114, 371282098103807432, 371282098104066517, 371282093345144300, 371282093505396463]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459310675312828, 362459311673114523⟩, ⟨204098600730361169, 204104647592067303⟩, true⟩

def words04 : List Nat := [371282106113844113, 371282106224189679, 371282106224384996, 371282103843205109, 371282102925312693, 371282102925605379, 371282105837099038, 371282111644534395, 371282116661403814, 371282116661672296]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362579642472625820, 362579643472777303⟩, ⟨(-873215223679914868), (-873209155775766306)⟩, true⟩

def words05 : List Nat := [371282123990912201, 371282133865839531, 371282148814561272, 371282153922197421, 371282157607293597, 371282161291643015, 371282171874169255, 371282176215265864, 371282187093485142, 371282197969398689]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362449136831868596, 362449137834360533⟩, ⟨296358985003978589, 296365073890491127⟩, true⟩

def words06 : List Nat := [371282207630974818, 371282207631234366, 371282206286817015, 371282211810688593, 371282217382664692, 371282217382924331, 371282206436545860, 371282192634603915, 371282178835632289, 371282177418963710]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362447058044345077, 362447059049175132⟩, ⟨315620247279266851, 315626357150716201⟩, true⟩

def words07 : List Nat := [371282182431481195, 371282191125095162, 371282199685923934, 371282199686188333, 371282199915891898, 371282201766178098, 371282213728845210, 371282213729105327, 371282210664561576, 371282206750416860]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362411095184441478, 362411096191603538⟩, ⟨638893035356026064, 638899166180948434⟩, true⟩

def words08 : List Nat := [371282203978739590, 371282203979028492, 371282202317340995, 371282205589060114, 371282206635082175, 371282206635342458, 371282191236360811, 371282178938558551, 371282166643356744, 371282163952024111]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362409037315496313, 362409038325037082⟩, ⟨657248600031647763, 657254752252953649⟩, true⟩

def words09 : List Nat := [371282156047899173, 371282147021917340, 371282137997835074, 371282134120062624, 371282124074167509, 371282114431410558, 371282104790711003, 371282095165468943, 371282074745673505, 371282066630842966]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk089
