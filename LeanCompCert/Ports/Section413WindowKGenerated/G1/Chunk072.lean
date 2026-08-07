import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk072

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465609452397560, 362465610084834881⟩, ⟨147438759977213515, 147441843808681815⟩, true⟩

def state01 : KState := ⟨⟨362421233485630941, 362421234119891323⟩, ⟨467217823653317489, 467220920620333179⟩, true⟩

def words00 : List Nat := [371286096173434871, 371286096173640290, 371286089320572062, 371286078695491470, 371286068073285315, 371286057913200188, 371286038130525666, 371286037544333457, 371286036958234481, 371286035911932979]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362617340883630219, 362617341519738523⟩, ⟨(-947515600559137838), (-947512490259113064)⟩, true⟩

def words01 : List Nat := [371286037113917266, 371286047299698891, 371286076649644576, 371286080469525985, 371286080980258219, 371286081490915736, 371286089873780173, 371286089874007725, 371286107102576800, 371286125276799995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483151781108371, 362483152419066458⟩, ⟨21601254072928356, 21604377737851520⟩, true⟩

def words02 : List Nat := [371286142085611405, 371286142085816801, 371286151076558345, 371286163152574212, 371286176963184172, 371286176963389361, 371286165335305604, 371286150718225904, 371286140576196276, 371286140576429923]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362462016282158846, 362462016921969942⟩, ⟨174514021409713429, 174517158481335367⟩, true⟩

def words03 : List Nat := [371286147623140649, 371286155081114644, 371286162622841182, 371286162623046649, 371286144786206018, 371286132548712431, 371286127108269865, 371286127108480311, 371286124831460151, 371286121501870679]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362548615241681372, 362548615883333414⟩, ⟨(-452463233703169605), (-452460083293628621)⟩, true⟩

def words04 : List Nat := [371286126854658470, 371286128203050021, 371286148543130081, 371286168877676488, 371286183517733129, 371286183517939034, 371286181174012981, 371286189487876142, 371286207595769124, 371286216202835052]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362536903807625272, 362536904451153922⟩, ⟨(-366873587194302715), (-366870423169948247)⟩, true⟩

def words05 : List Nat := [371286224901382786, 371286233597603027, 371286261229423617, 371286282397306614, 371286309146975157, 371286335889351633, 371286359585894041, 371286364373174966, 371286371334761129, 371286378294540515]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362447239859338847, 362447240504703299⟩, ⟨284742262526079185, 284745439888007173⟩, true⟩

def words06 : List Nat := [371286400311591063, 371286400311797268, 371286397138080529, 371286393780942957, 371286392665256684, 371286392665487493, 371286394844670350, 371286401218602863, 371286407690168961, 371286407690382530]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487229311061004, 362487229958297607⟩, ⟨(-6343902143826393), (-6340711162066997)⟩, true⟩

def words07 : List Nat := [371286406720150931, 371286411135581161, 371286423394272033, 371286423394478610, 371286410559789566, 371286393272072564, 371286375989025176, 371286372149448097, 371286358981250335, 371286359101112871]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362387432181513491, 362387432830614515⟩, ⟨720575982884140274, 720579187448588156⟩, true⟩

def words08 : List Nat := [371286359101269041, 371286358917714192, 371286343947900433, 371286345845717583, 371286351890742531, 371286351890949470, 371286332927280185, 371286309694733272, 371286286468475960, 371286277712294706]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362366385351056386, 362366386002020849⟩, ⟨874507272656259529, 874510490814657795⟩, true⟩

def words09 : List Nat := [371286264155326714, 371286263714529534, 371286263273787983, 371286258802114287, 371286238876785745, 371286224530552146, 371286214533974675, 371286214534182069, 371286198372089506, 371286181959666693]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk072
