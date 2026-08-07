import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511229540797168, 362511283243078811⟩, ⟨(-1577580848074852582), (-1575386237646006930)⟩, true⟩

def state01 : KState := ⟨⟨362496669119658325, 362496722840425546⟩, ⟨(-696671353551979970), (-694475624649153116)⟩, true⟩

def words00 : List Nat := [371285244580391837, 371285244679221345, 371285244949056848, 371285245219959288, 371285245571984540, 371285245574033421, 371285245561976196, 371285245550946026, 371285245799175386, 371285245991180795]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477177121117055, 362477230860347413⟩, ⟨482933924324767115, 485130770523645815⟩, true⟩

def words01 : List Nat := [371285246321280762, 371285246652224818, 371285246962324615, 371285246964374029, 371285246946361356, 371285246937073930, 371285247159075757, 371285247161125019, 371285247030966689, 371285246900838551]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492457485212194, 362492511242814257⟩, ⟨(-441821222399892534), (-439623264253462974)⟩, true⟩

def words02 : List Nat := [371285246910595910, 371285246985182282, 371285247260971624, 371285247537565788, 371285247770106258, 371285247772156436, 371285247863266735, 371285248047223870, 371285248341894472, 371285248464002517]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492253425981329, 362492307202227396⟩, ⟨(-429455335795738990), (-427256249033772260)⟩, true⟩

def words03 : List Nat := [371285248584751920, 371285248706171995, 371285248965777845, 371285249124959174, 371285249365421603, 371285249606722236, 371285249815521170, 371285249817571157, 371285249779014233, 371285249898102361]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484261790833625, 362484315585362050⟩, ⟨54380586922301623, 56580780591327523⟩, true⟩

def words04 : List Nat := [371285250196326180, 371285250198376325, 371285250133036157, 371285250029880261, 371285249925897296, 371285249904893471, 371285249840567095, 371285249936218169, 371285250030443807, 371285250032605508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501044205816037, 362501098018894940⟩, ⟨(-961838126193037548), (-959636809198973898)⟩, true⟩

def words05 : List Nat := [371285250243328954, 371285250470583035, 371285250895736832, 371285251131184111, 371285251277808956, 371285251425038210, 371285251631624769, 371285251703157824, 371285251966213984, 371285252230199262]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494150613710855, 362494204445297757⟩, ⟨(-544376880769051217), (-542174442836021791)⟩, true⟩

def words06 : List Nat := [371285252491173792, 371285252493224721, 371285252590945185, 371285252759029423, 371285253008257635, 371285253014243439, 371285253017303519, 371285253021067232, 371285253238663559, 371285253388804782]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476692629284576, 362476746479347027⟩, ⟨513157621982163322, 515361179074140474⟩, true⟩

def words07 : List Nat := [371285253587925699, 371285253787832349, 371285253968301732, 371285253970354503, 371285253844812915, 371285253804867131, 371285253860342040, 371285253862429069, 371285253734996857, 371285253596862282]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490487144437422, 362490541012849130⟩, ⟨(-322555903065175189), (-320351234283455489)⟩, true⟩

def words08 : List Nat := [371285253519456901, 371285253521720590, 371285253645628809, 371285253823165340, 371285253924725635, 371285253926777353, 371285253664962524, 371285253625059540, 371285253814252147, 371285253903636814]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477602982991504, 362477656870132853⟩, ⟨458213814402582191, 460419618107755407⟩, true⟩

def words09 : List Nat := [371285253986079324, 371285254069274455, 371285254280231239, 371285254356317448, 371285254513740471, 371285254671925421, 371285254830152024, 371285254832205061, 371285254676413236, 371285254553599978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605
