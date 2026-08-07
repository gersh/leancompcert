import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk068

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360688633529220979, 360688633771027765⟩, ⟨(-747836221001032534), (-747835105688675930)⟩, true⟩

def state01 : KState := ⟨⟨360677521994126411, 360677522236686915⟩, ⟨(-672903095055947726), (-672901974614585314)⟩, true⟩

def words00 : List Nat := [360578679394504743, 360578679394584071, 360578695704832259, 360578714581198106, 360578727690847135, 360578731118398387, 360578731118468992, 360578723620484846, 360578716124688355, 360578725881582733]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360341218124940546, 360341218368248795⟩, ⟨1618846991016613186, 1618848116553932538⟩, true⟩

def words01 : List Nat := [360578738269671099, 360578750654137187, 360578752055063522, 360578752055142804, 360578732316606509, 360578701022913016, 360578669738377880, 360578644877339139, 360578620936952473, 360578586127274299]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360670755962634255, 360670756206691258⟩, ⟨(-630416168230391076), (-630415037582788966)⟩, true⟩

def words02 : List Nat := [360578551327784604, 360578524858808162, 360578515797107251, 360578521919755198, 360578521919829973, 360578508413293270, 360578473844305744, 360578460572836497, 360578455322629199, 360578468834771658]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360634832730411234, 360634832975226873⟩, ⟨(-384649752966463120), (-384648617133710178)⟩, true⟩

def words03 : List Nat := [360578468834843678, 360578464498978911, 360578477093504903, 360578510620663258, 360578538414638145, 360578566200495480, 360578580401453116, 360578589574407017, 360578597797191949, 360578606017598791]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360790884982522174, 360790885228086977⟩, ⟨(-1452650811517739169), (-1452649670556882521)⟩, true⟩

def words04 : List Nat := [360578635448505959, 360578662668893835, 360578679070910061, 360578695468142679, 360578702225358401, 360578726365470728, 360578761043479796, 360578795711377551, 360578819582667749, 360578850536719749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360768118707019368, 360768118953338069⟩, ⟨(-1297804248333358826), (-1297803102204512562)⟩, true⟩

def words05 : List Nat := [360578873977863309, 360578897412188300, 360578908334637884, 360578911806041812, 360578911806115300, 360578897229873232, 360578889213697461, 360578907245621990, 360578934827568378, 360578962401493657]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360745044953089226, 360745045200167792⟩, ⟨(-1140486491685451383), (-1140485340340113207)⟩, true⟩

def words06 : List Nat := [360578979195027728, 360578985197434761, 360579012286363814, 360579039367424978, 360579060764498139, 360579061361373410, 360579061361446385, 360579045781998197, 360579035689110447, 360579059850096462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568142185870438, 360568142433701879⟩, ⟨76598593380880852, 76599749902313718⟩, true⟩

def words07 : List Nat := [360579105050433675, 360579150237633071, 360579181768528565, 360579214153300158, 360579232919986757, 360579251681236756, 360579268639195354, 360579277736630022, 360579277736701287, 360579276118280704]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360935120511825613, 360935120760413790⟩, ⟨(-2450552803575243151), (-2450551641843767179)⟩, true⟩

def words08 : List Nat := [360579274500313671, 360579283772888005, 360579316582110677, 360579349381817956, 360579361852252186, 360579372002369588, 360579393302362435, 360579414596196170, 360579452887784299, 360579504501257824]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360809239371543462, 360809239620894106⟩, ⟨(-1582559961088936440), (-1582558794100282496)⟩, true⟩

def words09 : List Nat := [360579545446029137, 360579586378929179, 360579640018300013, 360579704557058374, 360579754614531152, 360579804657500198, 360579837650923230, 360579850028898303, 360579883273831667, 360579916509156636]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk068
