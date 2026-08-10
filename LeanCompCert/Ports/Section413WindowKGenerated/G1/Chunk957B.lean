import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957A

def state06 : KState := ⟨⟨362497040644471692, 362497180070527494⟩, ⟨(-1151936232694399508), (-1142921858009854094)⟩, true⟩

def words05 : List Nat := [371285243839437581, 371285243968910286, 371285244142093623, 371285244262370306, 371285244387180655, 371285244513230951, 371285244628407575, 371285244665074829, 371285244791991352, 371285244920957107]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484948833208317, 362485088289111834⟩, ⟨6034861917982438, 15052094977473516⟩, true⟩

def words06 : List Nat := [371285245099194839, 371285245133088368, 371285245161804060, 371285245191623970, 371285245247966113, 371285245266713836, 371285245329121963, 371285245392886604, 371285245454842171, 371285245458319076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498276381129584, 362498415867358659⟩, ⟨(-1270405347284732329), (-1261385209792251693)⟩, true⟩

def words07 : List Nat := [371285245513681054, 371285245572383238, 371285245738524989, 371285245815280851, 371285245872721543, 371285245931254175, 371285246043953136, 371285246114211376, 371285246253993201, 371285246395231701]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492458753365531, 362492598269918079⟩, ⟨(-713208361457691880), (-704185319430141098)⟩, true⟩

def words08 : List Nat := [371285246514343109, 371285246517701613, 371285246598476258, 371285246696359460, 371285246825294907, 371285246830095297, 371285246832630691, 371285246827512974, 371285246921272208, 371285247001850827]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481120685507453, 362481260232321277⟩, ⟨372972259140740142, 381998200051189394⟩, true⟩

def words09 : List Nat := [371285247189990853, 371285247379539386, 371285247558476812, 371285247603676716, 371285247625103712, 371285247648145584, 371285247741308168, 371285247744674357, 371285247725250367, 371285247687436634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957B
