import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842A

def state06 : KState := ⟨⟨362498111803722927, 362498218691053997⟩, ⟨(-1093426214673470828), (-1087344951183686704)⟩, true⟩

def words05 : List Nat := [371285313138704172, 371285313281260120, 371285313516020525, 371285313579692171, 371285313607901131, 371285313637060746, 371285313794589966, 371285313892781444, 371285314047954002, 371285314204385388]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494597910674831, 362494704824359080⟩, ⟨(-797362861542121907), (-791279377394794505)⟩, true⟩

def words06 : List Nat := [371285314359732147, 371285314362657050, 371285314436333029, 371285314546082112, 371285314686446656, 371285314745992089, 371285314804205487, 371285314863356584, 371285315009968762, 371285315124730563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481494113210755, 362481601053300934⟩, ⟨306983746129908306, 313069455637973442⟩, true⟩

def words07 : List Nat := [371285315287315672, 371285315451116781, 371285315586717724, 371285315589645627, 371285315593659570, 371285315618998782, 371285315766349925, 371285315769275283, 371285315729214480, 371285315688512586]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494453858611646, 362494560824870430⟩, ⟨(-785280961817429950), (-779193046684600212)⟩, true⟩

def words08 : List Nat := [371285315731943877, 371285315771252483, 371285315932459009, 371285316094832894, 371285316234382127, 371285316259954293, 371285316342820620, 371285316427211289, 371285316628619438, 371285316741318395]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493208808535609, 362493315801412218⟩, ⟨(-680332177993790140), (-674242019109936536)⟩, true⟩

def words09 : List Nat := [371285316853201411, 371285316966058793, 371285317125956282, 371285317236804385, 371285317363373306, 371285317491084935, 371285317617812145, 371285317620738430, 371285317671847779, 371285317770319943]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842B
