import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473480784723582, 362473567055038595⟩, ⟨880350365970887278, 884778013208983926⟩, true⟩

def state01 : KState := ⟨⟨362494505392421436, 362494591686140506⟩, ⟨(-717585950727630014), (-713156524659389100)⟩, true⟩

def words00 : List Nat := [371285208739450497, 371285208742335378, 371285208798762881, 371285208915414809, 371285208998953327, 371285209001617269, 371285209023391824, 371285209088056357, 371285209279456698, 371285209405619800]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489470034368786, 362489556351934179⟩, ⟨(-334810820272982160), (-330379581524476012)⟩, true⟩

def words01 : List Nat := [371285209528689411, 371285209652609315, 371285209847549957, 371285209967943495, 371285210112064555, 371285210257216581, 371285210401415742, 371285210404033864, 371285210392580240, 371285210453017769]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473232487831714, 362473318828685147⟩, ⟨899658932819748619, 904091942047021589⟩, true⟩

def words02 : List Nat := [371285210601429655, 371285210604047976, 371285210522075543, 371285210440385582, 371285210357650757, 371285210328764526, 371285210212368730, 371285210169034970, 371285210124841134, 371285210081375494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502521335631954, 362502607700201024⟩, ⟨(-1327315255887379464), (-1322880443448235422)⟩, true⟩

def words03 : List Nat := [371285209943233710, 371285209962942905, 371285210137714647, 371285210169567591, 371285210171595000, 371285210158395048, 371285210242590614, 371285210301443921, 371285210532012883, 371285210763766098]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484200552159252, 362484286940416035⟩, ⟨65809721078420340, 70246334847984404⟩, true⟩

def words04 : List Nat := [371285210941135818, 371285210943755038, 371285210932640537, 371285210960904962, 371285211019799548, 371285211022419755, 371285210882023599, 371285210742568963, 371285210623573487, 371285210626607330]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk760
