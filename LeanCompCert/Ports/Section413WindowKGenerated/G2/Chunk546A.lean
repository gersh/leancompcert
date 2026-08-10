import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558472951369322, 360558491787846421⟩, ⟨1267973740849897930, 1268668630251682594⟩, true⟩

def state01 : KState := ⟨⟨360554462209683707, 360554481053299596⟩, ⟨1487008508849037103, 1487703788064453079⟩, true⟩

def words00 : List Nat := [360581727052104227, 360581726962149668, 360581726719311158, 360581726307926775, 360581725896426602, 360581725340740151, 360581724985476800, 360581724513324612, 360581724041106982, 360581723385987098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601755556671282, 360601774407446595⟩, ⟨(-1095975206021996198), (-1095279535794732596)⟩, true⟩

def words01 : List Nat := [360581722887757306, 360581722626504833, 360581722365033789, 360581722203333873, 360581722127905614, 360581721716540812, 360581721305045733, 360581721319469509, 360581721687221327, 360581722055131648]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610955890414238, 360610974748437620⟩, ⟨(-1598743006991416657), (-1598046940839640509)⟩, true⟩

def words02 : List Nat := [360581722123040707, 360581722123800301, 360581722201836278, 360581722408661541, 360581722409299736, 360581722489073997, 360581722489750228, 360581722402370621, 360581722561204151, 360581723097528070]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579970166086842, 360579989031252919⟩, ⟨94262280281311687, 94958736675087247⟩, true⟩

def words03 : List Nat := [360581723968074172, 360581724838733836, 360581725541706888, 360581726025574997, 360581726261477665, 360581726497562367, 360581726784066447, 360581726959404421, 360581726960090216, 360581726929069081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608749722286326, 360608768594628916⟩, ⟨(-1478300931095231068), (-1477604082541797678)⟩, true⟩

def words04 : List Nat := [360581727109282674, 360581727579619548, 360581728280340063, 360581728981181866, 360581729397159167, 360581729574890447, 360581730086750917, 360581730598830790, 360581731007702234, 360581731503220858]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546A
