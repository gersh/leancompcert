import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657A

def state06 : KState := ⟨⟨362494033704154923, 362494097568619979⟩, ⟨(-567846189438366195), (-565009640471282445)⟩, true⟩

def words05 : List Nat := [371285505178209738, 371285505104565236, 371285505145848915, 371285505180378658, 371285505284655214, 371285505389772663, 371285505473146161, 371285505475442152, 371285505570062099, 371285505703525603]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482005632581289, 362482069516964920⟩, ⟨223230826651270409, 226068685569878995⟩, true⟩

def words06 : List Nat := [371285506066816347, 371285506148472893, 371285506229186684, 371285506310619393, 371285506402408624, 371285506404877952, 371285506535569826, 371285506679128012, 371285506776095384, 371285506778414972]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495517565214731, 362495581469886588⟩, ⟨(-665508410412974550), (-662669217040846180)⟩, true⟩

def words07 : List Nat := [371285506877769276, 371285507030593211, 371285507292455850, 371285507294696861, 371285507248798102, 371285507166705373, 371285507230143447, 371285507289902934, 371285507444599453, 371285507600273161]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495348409446149, 362495412334328259⟩, ⟨(-654441090342828272), (-651600567436743432)⟩, true⟩

def words08 : List Nat := [371285507754771774, 371285507757014917, 371285507748734351, 371285507849116642, 371285507977016980, 371285507979298940, 371285507947690313, 371285507916701588, 371285508082348590, 371285508235478314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479923093191517, 362479987038304106⟩, ⟨360507721533719314, 363349575505295954⟩, true⟩

def words09 : List Nat := [371285508506185867, 371285508777819118, 371285509011157162, 371285509013399386, 371285509001207129, 371285509032267669, 371285509230418570, 371285509232660694, 371285509149662784, 371285509068326983]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657B
