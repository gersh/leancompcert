import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362443033068698740, 362443076121522921⟩, ⟨2274960908816505868, 2276543089428326524⟩, true⟩

def state01 : KState := ⟨⟨362474049148113476, 362474092217285636⟩, ⟨587586417681304833, 589169487707063453⟩, true⟩

def words00 : List Nat := [371284923572064153, 371284923142264540, 371284922542688982, 371284922281304796, 371284922019364924, 371284921745232475, 371284921168515143, 371284920849725293, 371284920546357190, 371284920548248825]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487457670580922, 362487500756412986⟩, ⟨(-142058792861548973), (-140474816285170547)⟩, true⟩

def words01 : List Nat := [371284920350629401, 371284920085331381, 371284919889389965, 371284919891422493, 371284919799962307, 371284919807242875, 371284919808622845, 371284919686669023, 371284919445528616, 371284919495203432]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476850160589581, 362476893262673379⟩, ⟨435291792552116108, 436876653634596502⟩, true⟩

def words02 : List Nat := [371284919881100284, 371284919882928264, 371284919819259682, 371284919755189632, 371284919690430544, 371284919640431458, 371284919516657072, 371284919586104157, 371284919655299422, 371284919657191744]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490443522406197, 362490486641073729⟩, ⟨(-304633929274045201), (-303048165460512695)⟩, true⟩

def words03 : List Nat := [371284919530254780, 371284919551805257, 371284919823968011, 371284919825801383, 371284919754258448, 371284919657726502, 371284919798987549, 371284919890262774, 371284919993789235, 371284920098110512]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491166964533335, 362491210099716983⟩, ⟨(-344103598322430284), (-342516935288582702)⟩, true⟩

def words04 : List Nat := [371284920173269161, 371284920175097995, 371284919846854119, 371284919852771410, 371284919961057945, 371284919962918659, 371284919790861989, 371284919619901357, 371284919612098530, 371284919729746026]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472114093198563, 362472157244840413⟩, ⟨693487806681000713, 695075365950435005⟩, true⟩

def words05 : List Nat := [371284920057782191, 371284920386529653, 371284920646636291, 371284920648469362, 371284920570750249, 371284920585091137, 371284920751312018, 371284920753141524, 371284920520939567, 371284920288651475]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482042081124569, 362482085249140724⟩, ⟨152785237311956453, 154373688407796403⟩, true⟩

def words06 : List Nat := [371284920055549354, 371284919995139954, 371284919910489968, 371284920022143281, 371284920078953650, 371284920080783420, 371284919732107869, 371284919494241033, 371284919352036913, 371284919353939840]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480321465306141, 362480364650003845⟩, ⟨246530370674386606, 248119730499157032⟩, true⟩

def words07 : List Nat := [371284919303278805, 371284919226734873, 371284919241894183, 371284919243945510, 371284919288077827, 371284919361665891, 371284919433490421, 371284919435320589, 371284919058228331, 371284918976921965]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448998101982674, 362449041303002250⟩, ⟨1953174704678831325, 1954764953803323175⟩, true⟩

def words08 : List Nat := [371284918910510766, 371284918912341040, 371284918480936489, 371284917989490422, 371284917497381950, 371284917034369012, 371284916403877587, 371284915989210783, 371284915573891112, 371284915132215011]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488999972532965, 362489043190078513⟩, ⟨(-226739906464415284), (-225148756757121708)⟩, true⟩

def words09 : List Nat := [371284914475114365, 371284914070555512, 371284913665079222, 371284913596582727, 371284913226509266, 371284912773027394, 371284912318782972, 371284912201666295, 371284912018188310, 371284912096029650]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544
