import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720A

def state06 : KState := ⟨⟨362488136309005361, 362488213546270488⟩, ⟨(-217069787090030092), (-213311026233775706)⟩, true⟩

def words05 : List Nat := [371285252818169268, 371285252787146357, 371285252913875233, 371285252979598022, 371285253102647677, 371285253226663033, 371285253350318495, 371285253352833894, 371285253356915795, 371285253401029182]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469843005713647, 362469920264975252⟩, ⟨1101239326871116371, 1104999672909222567⟩, true⟩

def words06 : List Nat := [371285253543067258, 371285253545539876, 371285253450658992, 371285253328483289, 371285253205360448, 371285253071872141, 371285252840884718, 371285252752803859, 371285252663911811, 371285252576240817]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488870699060715, 362488947980757520⟩, ⟨(-270159374486535245), (-266397411441962505)⟩, true⟩

def words07 : List Nat := [371285252365179225, 371285252317350409, 371285252409481238, 371285252411954148, 371285252298791907, 371285252166487849, 371285252090523501, 371285252093249772, 371285252120398108, 371285252174491764]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485717845345038, 362485795149356630⟩, ⟨(-42948213665162321), (-39184642055022289)⟩, true⟩

def words08 : List Nat := [371285252226972777, 371285252229449526, 371285252074629298, 371285252020328150, 371285251964840813, 371285251949253687, 371285251812484365, 371285251677094317, 371285251594805835, 371285251605196402]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490060410927084, 362490137737229050⟩, ⟨(-355972498557434354), (-352207319921605824)⟩, true⟩

def words09 : List Nat := [371285251806623405, 371285252009029489, 371285252170663601, 371285252206513126, 371285252299891726, 371285252394527160, 371285252610315546, 371285252681168695, 371285252750789152, 371285252821348250]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720B
