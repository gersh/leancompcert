import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492043473258648, 362492156076886866⟩, ⟨(-606532781576240869), (-599963718243466157)⟩, true⟩

def state01 : KState := ⟨⟨362478476482965699, 362478589113348824⟩, ⟨565715327411602974, 572286702512039712⟩, true⟩

def words00 : List Nat := [371285212270593669, 371285212273598528, 371285212233098302, 371285212189481403, 371285212144755618, 371285212106906498, 371285212009484944, 371285212021429812, 371285212032382320, 371285212035493392]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489091266982100, 362489203924496200⟩, ⟨(-351588126199315926), (-345014406573916132)⟩, true⟩

def words01 : List Nat := [371285211960905076, 371285211920863726, 371285211969479850, 371285211972485117, 371285211886562112, 371285211767197688, 371285211646550454, 371285211645802175, 371285211622989445, 371285211672536909]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479684889433167, 362479797574087217⟩, ⟨461363168350754111, 467939233547372621⟩, true⟩

def words02 : List Nat := [371285211721102800, 371285211724160823, 371285211730380268, 371285211802993158, 371285211913634998, 371285211916640992, 371285211865264925, 371285211777888374, 371285211689339988, 371285211657548370]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473326636443615, 362473439348206662⟩, ⟨1010975586256942537, 1017553994619833883⟩, true⟩

def words03 : List Nat := [371285211632985403, 371285211672326626, 371285211704293284, 371285211707303845, 371285211594596969, 371285211509955124, 371285211423701613, 371285211410444752, 371285211276390105, 371285211143609483]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475857682176552, 362475970420888396⟩, ⟨792207030611645044, 798787768565745656⟩, true⟩

def words04 : List Nat := [371285211009464983, 371285211010315683, 371285210943078132, 371285210917434086, 371285210890909674, 371285210835782907, 371285210601345531, 371285210489054709, 371285210375181803, 371285210302537509]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk864
