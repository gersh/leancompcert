import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502297943923164, 362502345387375834⟩, ⟨(-993394392118727826), (-991567605622609088)⟩, true⟩

def state01 : KState := ⟨⟨362489366405426451, 362489413866018266⟩, ⟨(-256235387093439773), (-254407623575808911)⟩, true⟩

def words00 : List Nat := [371284950133902194, 371284950223688597, 371284950311719488, 371284950400378323, 371284950544733967, 371284950546871218, 371284950807530623, 371284951080019588, 371284951355283722, 371284951435547378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503897512061707, 362503944989991556⟩, ⟨(-1084725850949860788), (-1082897098902426480)⟩, true⟩

def words01 : List Nat := [371284951772671655, 371284952110758278, 371284952569921698, 371284952698477690, 371284952757871207, 371284952817837616, 371284953013366953, 371284953122447645, 371284953456828323, 371284953792031113]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488908585679493, 362488956080975910⟩, ⟨(-229980934148944569), (-228151191774500033)⟩, true⟩

def words02 : List Nat := [371284954113809071, 371284954181408882, 371284954524779524, 371284954869202128, 371284955304958299, 371284955331349805, 371284955355952830, 371284955381186806, 371284955531846878, 371284955604186542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470784919077904, 362470832431706148⟩, ⟨803724427731723575, 805555158626577497⟩, true⟩

def words03 : List Nat := [371284955810834031, 371284956018266193, 371284956226446084, 371284956228368978, 371284956026653909, 371284955768354006, 371284955556099610, 371284955558026976, 371284955313132868, 371284955067726951]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491108597983508, 362491156127842307⟩, ⟨(-355633787523244123), (-353802073708216077)⟩, true⟩

def words04 : List Nat := [371284954881478365, 371284954883617129, 371284954791070578, 371284954772319665, 371284954752978794, 371284954686945039, 371284954345673934, 371284954313009361, 371284954511902111, 371284954622632789]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570A
