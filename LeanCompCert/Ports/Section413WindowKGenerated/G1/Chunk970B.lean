import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970A

def state06 : KState := ⟨⟨362481265638401955, 362481409023979719⟩, ⟨371329569426681086, 380725688177558400⟩, true⟩

def words05 : List Nat := [371285331414544426, 371285331568072685, 371285331687408071, 371285331690813619, 371285331668449471, 371285331642267680, 371285331675434981, 371285331678857053, 371285331641349872, 371285331604735722]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486184004790458, 362486327420865919⟩, ⟨(-106038135845095968), (-96639056828649080)⟩, true⟩

def words06 : List Nat := [371285331603832280, 371285331607651341, 371285331685457843, 371285331766152303, 371285331828971991, 371285331832378039, 371285331771001005, 371285331792719484, 371285331856839238, 371285331870631260]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487045004130086, 362487188451263600⟩, ⟨(-189606812107335429), (-180204718124535219)⟩, true⟩

def words07 : List Nat := [371285331878584822, 371285331887716646, 371285332001658154, 371285332064009177, 371285332126914265, 371285332191137910, 371285332253835865, 371285332257242330, 371285332197339599, 371285332220712571]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483569651484604, 362483713129016904⟩, ⟨147795131360574525, 157200176611836751⟩, true⟩

def words08 : List Nat := [371285332348363817, 371285332351770347, 371285332338255450, 371285332295950378, 371285332252353507, 371285332242053885, 371285332207522752, 371285332226289177, 371285332243522855, 371285332247119818]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491768477425336, 362491911985685814⟩, ⟨(-648249045474472257), (-638841016670116363)⟩, true⟩

def words09 : List Nat := [371285332311303885, 371285332393941954, 371285332570148012, 371285332623867053, 371285332660643103, 371285332698511703, 371285332727319158, 371285332731074283, 371285332774710093, 371285332846267373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970B
