import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362510899997962540, 362510949542167070⟩, ⟨(-1512868569088408222), (-1510920774272496404)⟩, true⟩

def state01 : KState := ⟨⟨362488473357003662, 362488522918696013⟩, ⟨(-207559777657212999), (-205610964958779081)⟩, true⟩

def words00 : List Nat := [371284989650376894, 371284989757526626, 371284989826152404, 371284989895405927, 371284989980987212, 371284989983153122, 371284990187920221, 371284990439549792, 371284990689124001, 371284990751838224]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515667741072300, 362515717320545717⟩, ⟨(-1790645274094877052), (-1788695426275074736)⟩, true⟩

def words01 : List Nat := [371284991109326385, 371284991467880100, 371284992035017447, 371284992321315752, 371284992562228002, 371284992803765387, 371284993339902653, 371284993748639373, 371284994277711594, 371284994807598927]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362501480761595346, 362501530358817545⟩, ⟨(-964689052368285975), (-962738171121948449)⟩, true⟩

def words02 : List Nat := [371284995337833827, 371284995526546733, 371284995823339512, 371284996121157126, 371284996431734009, 371284996498532432, 371284996562393129, 371284996626890070, 371284996985935710, 371284997272126231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500019515239022, 362500069130217715⟩, ⟨(-879524734787515034), (-877572819494670722)⟩, true⟩

def words03 : List Nat := [371284997852699921, 371284998434072150, 371284998936404519, 371284999176006858, 371284999482283471, 371284999789499942, 371285000390984836, 371285000653093906, 371285000913310177, 371285001174319042]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505774995368917, 362505824627929946⟩, ⟨(-1214669596243557467), (-1212716656864116049)⟩, true⟩

def words04 : List Nat := [371285001699757230, 371285002103735319, 371285002802081277, 371285003501184904, 371285004104229283, 371285004314592160, 371285004612601049, 371285004911633890, 371285005455816529, 371285005815259535]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582A
