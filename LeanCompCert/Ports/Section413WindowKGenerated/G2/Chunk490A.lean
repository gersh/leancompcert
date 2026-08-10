import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533885864642827, 360533900902258947⟩, ⟨2355360358520483319, 2355858260152055283⟩, true⟩

def state01 : KState := ⟨⟨360572093852440819, 360572108896425663⟩, ⟨482950840738008319, 483449054468944569⟩, true⟩

def words00 : List Nat := [360581978661630376, 360581977861725771, 360581977272318418, 360581977098189268, 360581976924025098, 360581976340072744, 360581975455131161, 360581974561968358, 360581973668644102, 360581973190538476]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567438865758665, 360567453916172751⟩, ⟨711090935074518168, 711589463934174708⟩, true⟩

def words01 : List Nat := [360581972989875078, 360581972489566613, 360581971989150019, 360581971698754019, 360581971699319156, 360581971612361656, 360581971525329385, 360581971230920156, 360581970520471030, 360581970225106537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360528925523566028, 360528940580346974⟩, ⟨2599120854145210515, 2599619695140051053⟩, true⟩

def words02 : List Nat := [360581969929537937, 360581969521054642, 360581968809091220, 360581967828321659, 360581966847482988, 360581965638713367, 360581964640061798, 360581963705385460, 360581962770660056, 360581961581675550]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565493941643693, 360565509004800896⟩, ⟨806005845545592323, 806504999199687261⟩, true⟩

def words03 : List Nat := [360581960500844600, 360581959834918424, 360581959168813871, 360581958917504137, 360581958250564761, 360581957202307047, 360581956153958306, 360581955520433646, 360581955199970090, 360581954865306600]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360544882191295533, 360544897260900831⟩, ⟨1816936779932832540, 1817436249832163090⟩, true⟩

def words04 : List Nat := [360581954530564866, 360581953985990717, 360581953550443605, 360581953529621819, 360581953508623278, 360581953233530551, 360581952655063131, 360581951869443486, 360581951083742421, 360581949987706788]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490A
