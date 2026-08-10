import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836A

def state06 : KState := ⟨⟨362496445419705627, 362496550732211666⟩, ⟨(-945197061353195801), (-939248020868592515)⟩, true⟩

def words05 : List Nat := [371285322880996341, 371285323019020932, 371285323298470675, 371285323404122318, 371285323477149015, 371285323551056218, 371285323619268730, 371285323626268322, 371285323762435531, 371285323899866026]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491764409942905, 362491869748647926⟩, ⟨(-553595421308024726), (-547644188886669270)⟩, true⟩

def words06 : List Nat := [371285324034161130, 371285324037063972, 371285324105460872, 371285324213716358, 371285324343628292, 371285324346550394, 371285324348412223, 371285324346498917, 371285324458030735, 371285324539568476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488423355540676, 362488528720432807⟩, ⟨(-274010843261211859), (-268057419630876647)⟩, true⟩

def words07 : List Nat := [371285324678728205, 371285324819057894, 371285324958643567, 371285324987381770, 371285325057411932, 371285325128850074, 371285325272229092, 371285325313632176, 371285325354083528, 371285325395668155]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493382673777699, 362493488064628542⟩, ⟨(-689024702308966002), (-683069106318153414)⟩, true⟩

def words08 : List Nat := [371285325497642542, 371285325529614590, 371285325681795737, 371285325835128658, 371285325951205122, 371285325954108391, 371285325925375699, 371285325974715493, 371285326165263474, 371285326265793325]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486258156033023, 362486363573385752⟩, ⟨(-92685218611682089), (-86727404550046629)⟩, true⟩

def words09 : List Nat := [371285326344437394, 371285326424063675, 371285326632458959, 371285326800671583, 371285326999631899, 371285327199733983, 371285327387466793, 371285327390370604, 371285327400069209, 371285327416057285]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836B
