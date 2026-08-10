import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500257185441070, 362500380319539543⟩, ⟨(-1384704822928262586), (-1377205763271143676)⟩, true⟩

def state01 : KState := ⟨⟨362499665519947028, 362499788682458008⟩, ⟨(-1331330852832893528), (-1323829230222684546)⟩, true⟩

def words00 : List Nat := [371285112301712964, 371285112393296998, 371285112606670315, 371285112821637606, 371285113072577550, 371285113220708055, 371285113366619866, 371285113513600351, 371285113706795724, 371285113873064224]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488960254569291, 362489083445407195⟩, ⟨(-365526392407863466), (-358022214282634644)⟩, true⟩

def words01 : List Nat := [371285114081091206, 371285114290359025, 371285114498399286, 371285114563841044, 371285114665841195, 371285114769527359, 371285114994277288, 371285115071279943, 371285115117627725, 371285115165136719]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498503951423541, 362498627170458278⟩, ⟨(-1226587946240360404), (-1219081224050819216)⟩, true⟩

def words02 : List Nat := [371285115323391759, 371285115439274731, 371285115604778234, 371285115771564014, 371285115917153375, 371285115920302224, 371285116026646037, 371285116143883435, 371285116347856780, 371285116500909556]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493470102475422, 362493593350222763⟩, ⟨(-772357145612500560), (-764847832542222756)⟩, true⟩

def words03 : List Nat := [371285116649788129, 371285116799750157, 371285116984505030, 371285117108909833, 371285117269517640, 371285117431309350, 371285117568540961, 371285117571690248, 371285117638906698, 371285117736781620]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487968082508098, 362488091358302601⟩, ⟨(-275839899010998561), (-268328054821509301)⟩, true⟩

def words04 : List Nat := [371285117900421256, 371285117903570633, 371285117903778865, 371285117892921546, 371285117903979375, 371285117907467452, 371285117989943229, 371285118094934427, 371285118190988538, 371285118227203539]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902A
