import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929A

def state06 : KState := ⟨⟨362496819682241228, 362496950772259701⟩, ⟨(-1107374418443881234), (-1099146695191007884)⟩, true⟩

def words05 : List Nat := [371285126584484094, 371285126669210404, 371285126797565783, 371285126800817628, 371285126775189738, 371285126732100549, 371285126756856833, 371285126771891222, 371285126901290517, 371285127032248396]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487462808195518, 362487593927544959⟩, ⟨(-237555924487163962), (-229325474476686224)⟩, true⟩

def words06 : List Nat := [371285127141374276, 371285127144627176, 371285127161282424, 371285127210697231, 371285127293951011, 371285127297210397, 371285127284797616, 371285127246751833, 371285127262785183, 371285127293062415]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487734108088210, 362487865256695533⟩, ⟨(-262730012859845947), (-254496842593457447)⟩, true⟩

def words07 : List Nat := [371285127427422850, 371285127563099472, 371285127683909406, 371285127729426741, 371285127808886505, 371285127890015000, 371285128075252474, 371285128107363817, 371285128139255583, 371285128172317075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486702257134923, 362486833434901496⟩, ⟨(-166784508744203691), (-158548627106263669)⟩, true⟩

def words08 : List Nat := [371285128233607577, 371285128238570024, 371285128289432871, 371285128341633986, 371285128374413246, 371285128377673455, 371285128317206782, 371285128347674908, 371285128424242739, 371285128445955187]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489227119361644, 362489358326762747⟩, ⟨(-401568265251007821), (-393329627750623187)⟩, true⟩

def words09 : List Nat := [371285128461138744, 371285128477468187, 371285128608087277, 371285128698941367, 371285128792914963, 371285128888064875, 371285128982777853, 371285128986031523, 371285128971857201, 371285129021403121]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929B
