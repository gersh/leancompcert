import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760A

def state06 : KState := ⟨⟨362477146244279749, 362477232656063814⟩, ⟨602373389532779173, 606811792676417699⟩, true⟩

def words05 : List Nat := [371285210744832039, 371285210876241185, 371285210994818856, 371285210997456204, 371285210960839858, 371285210908188082, 371285210925846733, 371285210928473630, 371285210825257317, 371285210723282805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474637726557168, 362474724161821891⟩, ⟨793244538098493812, 797684727302679574⟩, true⟩

def words06 : List Nat := [371285210637328621, 371285210640265784, 371285210665133590, 371285210736766244, 371285210757357374, 371285210759977851, 371285210574681245, 371285210478082687, 371285210380158808, 371285210355160957]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476993483178233, 362477079942352071⟩, ⟨614046319670189405, 618488327757859113⟩, true⟩

def words07 : List Nat := [371285210219272072, 371285210084292930, 371285209962148343, 371285209965038022, 371285209907192254, 371285209862730535, 371285209817338606, 371285209770654373, 371285209492924240, 371285209389352043]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470054125790673, 362470140608324851⟩, ⟨1142046686178270021, 1146490471644690495⟩, true⟩

def words08 : List Nat := [371285209350067437, 371285209352688353, 371285209210976517, 371285209036034327, 371285208860112232, 371285208737805122, 371285208527897952, 371285208408389662, 371285208287985010, 371285208166107013]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489101332105432, 362489187838290688⟩, ⟨(-307344324224889308), (-302898739029744858)⟩, true⟩

def words09 : List Nat := [371285207969864420, 371285207947564492, 371285208045906896, 371285208048528160, 371285207942444931, 371285207814712642, 371285207685906809, 371285207629018178, 371285207562843461, 371285207618069801]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760B
