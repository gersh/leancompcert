import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489166264406961, 362489234942374504⟩, ⟨(-260765333826775706), (-257606581112618396)⟩, true⟩

def state01 : KState := ⟨⟨362472935358501529, 362473004057208916⟩, ⟨844624013810384877, 847784179016584967⟩, true⟩

def words00 : List Nat := [371285452344250143, 371285452346583501, 371285452241683253, 371285452085860332, 371285451929130507, 371285451823767477, 371285451609677736, 371285451517757276, 371285451425074994, 371285451336301804]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486582938978619, 362486651658744997⟩, ⟨(-84936477412828135), (-81774877775487347)⟩, true⟩

def words01 : List Nat := [371285451187754300, 371285451223239718, 371285451472802366, 371285451475129651, 371285451437716094, 371285451375100756, 371285451311589962, 371285451302731630, 371285451202811500, 371285451223082346]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471439281222183, 362471508021997442⟩, ⟨946655306697438793, 949818337567669841⟩, true⟩

def words02 : List Nat := [371285451227286751, 371285451229614319, 371285450946523930, 371285450768929631, 371285450590169378, 371285450475870066, 371285450128186105, 371285449781498732, 371285449433841644, 371285449286309312]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474119534707922, 362474188296440462⟩, ⟨764057317682906252, 767221776481026834⟩, true⟩

def words03 : List Nat := [371285449083291380, 371285448971440540, 371285448858836320, 371285448745635045, 371285448489068365, 371285448299315608, 371285448108333981, 371285448103780974, 371285447950966754, 371285447788317202]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494503535173342, 362494572317740928⟩, ⟨(-624973528514983223), (-621807649911112481)⟩, true⟩

def words04 : List Nat := [371285447674580051, 371285447677146628, 371285447785732750, 371285447938216952, 371285447997136831, 371285447999476609, 371285447919051244, 371285447988398925, 371285448211877603, 371285448348174655]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk681A
