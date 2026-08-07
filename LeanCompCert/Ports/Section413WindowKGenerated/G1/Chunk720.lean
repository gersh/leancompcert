import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491641801228576, 362491718904950029⟩, ⟨(-469320132961333221), (-465570991282018487)⟩, true⟩

def state01 : KState := ⟨⟨362489813104607478, 362489890230351727⟩, ⟨(-337589844039770795), (-333839116604339447)⟩, true⟩

def words00 : List Nat := [371285252990390687, 371285253113528883, 371285253236421017, 371285253360122477, 371285253541260586, 371285253656040115, 371285253856401620, 371285254057775430, 371285254217281744, 371285254284223992]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502828880530551, 362502906028590851⟩, ⟨(-1274925377661982164), (-1271173043133402054)⟩, true⟩

def words01 : List Nat := [371285254526999114, 371285254771029298, 371285255109843748, 371285255192550142, 371285255243576122, 371285255295449929, 371285255445544789, 371285255500771280, 371285255747525475, 371285255995362579]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475632040671694, 362475709211040744⟩, ⟨683896025116925691, 687649966435789979⟩, true⟩

def words02 : List Nat := [371285256242724456, 371285256245195692, 371285256305088113, 371285256377577110, 371285256483340903, 371285256485812200, 371285256334899149, 371285256175791034, 371285256015694278, 371285255927220611]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362456303562461479, 362456380755093478⟩, ⟨2076321428249211295, 2080076973280919479⟩, true⟩

def words03 : List Nat := [371285255856359788, 371285255919074169, 371285255978578922, 371285255981050401, 371285255783679442, 371285255645913204, 371285255506889597, 371285255407248643, 371285255070000991, 371285254671990771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485212844221431, 362485290058992093⟩, ⟨(-6440514072682897), (-2683374061289607)⟩, true⟩

def words04 : List Nat := [371285254272869229, 371285254038997877, 371285253707587885, 371285253569689940, 371285253431017785, 371285253263456184, 371285252961569075, 371285252853463484, 371285252813191875, 371285252816288158]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk720
