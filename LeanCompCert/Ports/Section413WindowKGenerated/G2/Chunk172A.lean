import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk172A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360544552938615981, 360544554632416143⟩, ⟨672263630000701366, 672283351420880372⟩, true⟩

def state01 : KState := ⟨⟨360759203080029255, 360759204775885044⟩, ⟨(-3020827917001958028), (-3020808160214874196)⟩, true⟩

def words00 : List Nat := [360583638631407552, 360583640850180960, 360583646435502907, 360583652020219408, 360583654514429654, 360583657132331972, 360583663115350791, 360583669097739823, 360583678444444292, 360583688643166732]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360678301592610198, 360678303290544188⟩, ⟨(-1628111050430767150), (-1628091257867467114)⟩, true⟩

def words01 : List Nat := [360583697145066739, 360583705646003713, 360583714055599335, 360583724635201696, 360583732979950879, 360583741323765007, 360583747965602974, 360583751268634914, 360583756759637364, 360583762250078044]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604758332685248, 360604760032673289⟩, ⟨(-361387201862007670), (-361367373917876754)⟩, true⟩

def words02 : List Nat := [360583768810265136, 360583773173418700, 360583775843689734, 360583778513674569, 360583779049852395, 360583782391960720, 360583784452437234, 360583786512712983, 360583786882481319, 360583788099882513]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360748139393796254, 360748141095843881⟩, ⟨(-2832655692742310162), (-2832635829301131424)⟩, true⟩

def words03 : List Nat := [360583792672621467, 360583797244893202, 360583803213995529, 360583809299903790, 360583812494676589, 360583815689094204, 360583819361848931, 360583825541795454, 360583835073036776, 360583844603221578]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360697320512280827, 360697322216409826⟩, ⟨(-1956787084586922361), (-1956767185252602509)⟩, true⟩

def words04 : List Nat := [360583851496023432, 360583856669151891, 360583863868948718, 360583871067976157, 360583877387299299, 360583880380769859, 360583881688516914, 360583882996141392, 360583886437305362, 360583893013160589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk172A
