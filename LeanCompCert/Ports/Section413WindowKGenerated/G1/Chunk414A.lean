import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500826756757469, 362500851145911154⟩, ⟨(-653061597643214124), (-652379328020863262)⟩, true⟩

def state01 : KState := ⟨⟨362482643561178769, 362482667962444247⟩, ⟨99832234555987297, 100515005669102419⟩, true⟩

def words00 : List Nat := [371285094379144091, 371285094490490638, 371285094537000642, 371285094583964258, 371285094639210811, 371285094640710166, 371285094727238881, 371285095014400173, 371285095273415186, 371285095274824569]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509708536064347, 362509732949642873⟩, ⟨(-1020990747483534083), (-1020307466426957493)⟩, true⟩

def words01 : List Nat := [371285095741273815, 371285096267035862, 371285097374774414, 371285097706443742, 371285097854871659, 371285098003722019, 371285098679710731, 371285099144666747, 371285099740339100, 371285100336561901]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500980136849016, 362501004562704141⟩, ⟨(-659488638952582601), (-658804849334947923)⟩, true⟩

def words02 : List Nat := [371285100932192790, 371285100933554553, 371285101114577104, 371285101414791190, 371285101894585911, 371285102060408377, 371285102224641231, 371285102389303792, 371285102923465310, 371285103308828180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466531147702161, 362466555585850465⟩, ⟨768000855314605631, 768685154301446659⟩, true⟩

def words03 : List Nat := [371285104075877754, 371285104843451289, 371285105492027484, 371285105493389638, 371285105413630320, 371285105462667936, 371285105810384438, 371285105811746668, 371285105384083043, 371285104938029554]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488518433950936, 362488542884286949⟩, ⟨(-143187048875238941), (-142502244767342737)⟩, true⟩

def words04 : List Nat := [371285104491346222, 371285104470383004, 371285104425968715, 371285104695617045, 371285104870782650, 371285104872151105, 371285104615467515, 371285104557435060, 371285104951758745, 371285105036110371]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414A
