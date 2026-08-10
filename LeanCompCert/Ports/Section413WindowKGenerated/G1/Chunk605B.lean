import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605B
