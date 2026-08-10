import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470790434037642, 362470925480127054⟩, ⟨1334499338524611132, 1343097475770324406⟩, true⟩

def state01 : KState := ⟨⟨362482562015945431, 362482697091594315⟩, ⟨224399624081516428, 233000548935205818⟩, true⟩

def words00 : List Nat := [371285168146556015, 371285168103535434, 371285168020867117, 371285167996768643, 371285167971531526, 371285167929606412, 371285167752301475, 371285167689160440, 371285167669756202, 371285167673175645]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487224176224453, 362487359282080068⟩, ⟨(-215320952103327470), (-206717178304726524)⟩, true⟩

def words01 : List Nat := [371285167649516858, 371285167606057157, 371285167601696725, 371285167605626597, 371285167628836279, 371285167653288722, 371285167670171749, 371285167673532788, 371285167619946913, 371285167647361345]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479542170898210, 362479677306129080⟩, ⟨509301053714304250, 517907598341493636⟩, true⟩

def words02 : List Nat := [371285167785286882, 371285167788590335, 371285167776924532, 371285167756577232, 371285167735054051, 371285167701207384, 371285167639520191, 371285167667407952, 371285167683270116, 371285167686690318]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487891498541169, 362488026663653224⟩, ⟨(-278313482740825730), (-269704119273912020)⟩, true⟩

def words03 : List Nat := [371285167684956152, 371285167743171088, 371285167854372376, 371285167857676534, 371285167830188045, 371285167790087400, 371285167787789265, 371285167791468303, 371285167807741895, 371285167841727721]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486968232061146, 362487103426965703⟩, ⟨(-191252085794348505), (-182639911552188223)⟩, true⟩

def words04 : List Nat := [371285167858266587, 371285167861572214, 371285167746955406, 371285167746488648, 371285167773930453, 371285167777297516, 371285167736239053, 371285167672669941, 371285167653050968, 371285167677354653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943A
