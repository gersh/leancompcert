import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567434416091058, 360567474919856294⟩, ⟨1160921137450929929, 1163079516237292683⟩, true⟩

def state01 : KState := ⟨⟨360563363966206856, 360563404480582055⟩, ⟨1482070777067470389, 1484229993034620893⟩, true⟩

def words00 : List Nat := [360582215919186299, 360582215893896929, 360582215708189322, 360582215399574779, 360582215090765048, 360582214711902822, 360582214413039829, 360582214185516413, 360582213957876845, 360582213630157960]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588649312073605, 360588689837103061⟩, ⟨(-513415562551324029), (-511255505802967107)⟩, true⟩

def words01 : List Nat := [360582213392726215, 360582213151630486, 360582212910200084, 360582212680377058, 360582212506087765, 360582212194564632, 360582211882833632, 360582211682364726, 360582211687104157, 360582211770355263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574886158025755, 360574926693797605⟩, ⟨572682948495924887, 574843853085927803⟩, true⟩

def words02 : List Nat := [360582211771370845, 360582211745005538, 360582211558177572, 360582211415846190, 360582211273244069, 360582210964074422, 360582210655986397, 360582210267735549, 360582209879278573, 360582209651520726]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554313845739973, 360554354392147952⟩, ⟨2196590713869422532, 2198752458022040350⟩, true⟩

def words03 : List Nat := [360582209560164843, 360582209523400381, 360582209486494442, 360582209363232217, 360582209128138547, 360582208853348390, 360582208578218141, 360582208435557063, 360582208207953480, 360582207856272883]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583996305157924, 360584036862212454⟩, ⟨(-146632953393622872), (-144470368750319410)⟩, true⟩

def words04 : List Nat := [360582207504345536, 360582207313008093, 360582207261607151, 360582207297799138, 360582207298841541, 360582207204006497, 360582207113628766, 360582207048412596, 360582206982854733, 360582206988382480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789A
