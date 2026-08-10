import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502084722730334, 362502149478315486⟩, ⟨(-1104100865125136515), (-1101205519715743573)⟩, true⟩

def state01 : KState := ⟨⟨362489396622888945, 362489461398827528⟩, ⟨(-264097712585219367), (-261201019672687231)⟩, true⟩

def words00 : List Nat := [371285515458180793, 371285515460438006, 371285515624621876, 371285515812395771, 371285516068904453, 371285516136271987, 371285516186972446, 371285516238463650, 371285516357442067, 371285516419599414]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471930270791641, 362471995067054128⟩, ⟨892495738138968956, 895393776799484396⟩, true⟩

def words01 : List Nat := [371285516684420920, 371285516950132088, 371285517172151298, 371285517174408692, 371285517092433329, 371285516997851772, 371285516969777088, 371285516972034779, 371285516769377808, 371285516567760856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483189406381984, 362483254222823433⟩, ⟨146921295221839380, 149820670238589684⟩, true⟩

def words02 : List Nat := [371285516388715009, 371285516391238117, 371285516463609209, 371285516596040825, 371285516691635194, 371285516693893053, 371285516485566356, 371285516373573740, 371285516347470162, 371285516349808766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486834503673376, 362486899340745074⟩, ⟨(-94504687819202889), (-91603946364135115)⟩, true⟩

def words03 : List Nat := [371285516317370602, 371285516229510438, 371285516256404052, 371285516314242920, 371285516412520856, 371285516511634951, 371285516610163408, 371285516612421940, 371285516428064456, 371285516451803722]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478969943676719, 362479034800886886⟩, ⟨426497972221906391, 429400047752869067⟩, true⟩

def words04 : List Nat := [371285516569446003, 371285516571719889, 371285516485307659, 371285516392260937, 371285516298372533, 371285516275279213, 371285516209388128, 371285516273448357, 371285516308700023, 371285516311041647]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662A
