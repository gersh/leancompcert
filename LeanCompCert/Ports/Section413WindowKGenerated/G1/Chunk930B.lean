import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930A

def state06 : KState := ⟨⟨362486515199875820, 362486646583234619⟩, ⟨(-149357034477828117), (-141102027609263289)⟩, true⟩

def words05 : List Nat := [371285130836409444, 371285130709896613, 371285130582088769, 371285130571187536, 371285130515142056, 371285130481328915, 371285130446369277, 371285130411992249, 371285130331292067, 371285130351648786]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481362991715161, 362481494404015928⟩, ⟨330155636756891840, 338413337117150560⟩, true⟩

def words06 : List Nat := [371285130455664807, 371285130466918150, 371285130470675261, 371285130475561398, 371285130483738047, 371285130487326703, 371285130462676978, 371285130490995912, 371285130516868800, 371285130520241535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490594472548332, 362490725914365965⟩, ⟨(-529062781938072356), (-520802334296233630)⟩, true⟩

def words07 : List Nat := [371285130503271904, 371285130527157533, 371285130649917204, 371285130653173834, 371285130635705625, 371285130593796253, 371285130620623462, 371285130636285758, 371285130698644964, 371285130762462825]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495051433410088, 362495182904587167⟩, ⟨(-943980931267798493), (-935717750695969825)⟩, true⟩

def words08 : List Nat := [371285130810545139, 371285130813824056, 371285130816029413, 371285130877604922, 371285130972901308, 371285130987570393, 371285131002011094, 371285131017575329, 371285131147180735, 371285131258878173]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488301922867332, 362488433423399354⟩, ⟨(-315595230456967101), (-307329317090747761)⟩, true⟩

def words09 : List Nat := [371285131472633055, 371285131687691763, 371285131878696548, 371285131929622918, 371285132006078323, 371285132084212967, 371285132275986279, 371285132315022296, 371285132352914546, 371285132392077556]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930B
