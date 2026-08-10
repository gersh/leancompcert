import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk525A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568323587522096, 360568340947491854⟩, ⟨719178470071085627, 719794281602859639⟩, true⟩

def state01 : KState := ⟨⟨360544729207123180, 360544746573936403⟩, ⟨1957992264883036952, 1958608435731709784⟩, true⟩

def words00 : List Nat := [360582051155087714, 360582051155814955, 360582050895500149, 360582050299729970, 360582049703863860, 360582049017423189, 360582048510899321, 360582047849704138, 360582047188455708, 360582046296574600]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604461790877893, 360604479164557954⟩, ⟨(-1178872292626643412), (-1178255761166644706)⟩, true⟩

def words01 : List Nat := [360582045586840693, 360582045239242760, 360582044891446366, 360582044666150461, 360582044660211872, 360582044347663800, 360582044083547236, 360582044315611422, 360582044743367860, 360582045171275903]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577718061597999, 360577735442213832⟩, ⟨225609657576814358, 226226553337496630⟩, true⟩

def words02 : List Nat := [360582045272027284, 360582045272754923, 360582045011829479, 360582044998382774, 360582044984741281, 360582044725066161, 360582044103747318, 360582043301448031, 360582042499027086, 360582042058496671]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536543796292982, 360536561183758526⟩, ⟨2388771107882408063, 2389388363492230943⟩, true⟩

def words03 : List Nat := [360582042178476718, 360582042380571860, 360582042381229298, 360582042352542080, 360582041962273648, 360582041286985242, 360582040611503811, 360582040222618481, 360582039558373217, 360582038693531885]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574464240406393, 360574481634755787⟩, ⟨396386544346605881, 397004161666633013⟩, true⟩

def words04 : List Nat := [360582037828558135, 360582037325291321, 360582037236362372, 360582037373043012, 360582037373714848, 360582037223189514, 360582037113977954, 360582036887232503, 360582036660291729, 360582036423750395]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk525A
