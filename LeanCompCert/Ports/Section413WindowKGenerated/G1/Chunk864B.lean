import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864A

def state06 : KState := ⟨⟨362478073070808855, 362478185836845653⟩, ⟨600699869639563619, 607282969975450725⟩, true⟩

def words05 : List Nat := [371285210197904606, 371285210094370254, 371285210016558769, 371285210019906492, 371285209984686998, 371285209989756148, 371285209992045990, 371285209966972237, 371285209774765542, 371285209697243241]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477478159757271, 362477590952561390⟩, ⟨652175061508317019, 658760476286636365⟩, true⟩

def words06 : List Nat := [371285209670465117, 371285209673480519, 371285209591205495, 371285209508681123, 371285209424905189, 371285209383225408, 371285209295273199, 371285209320335480, 371285209322590083, 371285209322820285]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487012974005822, 362487125794076059⟩, ⟨(-172383712466085126), (-165795939852072608)⟩, true⟩

def words07 : List Nat := [371285209236806188, 371285209169244578, 371285209139026179, 371285209142033767, 371285209005100041, 371285208849123411, 371285208691937375, 371285208669701981, 371285208631308093, 371285208656903131]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478042852179241, 362478155699377298⟩, ⟨603383974122202238, 609974092890116814⟩, true⟩

def words08 : List Nat := [371285208680262381, 371285208683290866, 371285208615897317, 371285208648802492, 371285208683563416, 371285208686571858, 371285208559675261, 371285208423355604, 371285208285789901, 371285208238316946]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470709946592776, 362470822820879128⟩, ⟨1237700127792859414, 1244292589562636184⟩, true⟩

def words09 : List Nat := [371285208210845963, 371285208266168763, 371285208294176382, 371285208297185375, 371285208164643046, 371285208074517609, 371285208002477101, 371285208005486166, 371285207869252691, 371285207706307598]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864B
