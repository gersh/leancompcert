import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360523294443792961, 360523299131309788⟩, ⟨1653140091759009094, 1653228865072400786⟩, true⟩

def state01 : KState := ⟨⟨360612837568315986, 360612842259314355⟩, ⟨(-854397268972048504), (-854308398157883890)⟩, true⟩

def words00 : List Nat := [360582340911011628, 360582340075241281, 360582340792983042, 360582341524089694, 360582341524429902, 360582341258229526, 360582341313677630, 360582341369228215, 360582342137612997, 360582343226857182]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607341909513760, 360607346604027159⟩, ⟨(-700404037040882930), (-700315067753506826)⟩, true⟩

def words01 : List Nat := [360582343676569412, 360582344126289935, 360582345545456845, 360582348110693018, 360582349954870046, 360582351798975213, 360582352689417015, 360582352689786305, 360582353203615269, 360582354095988420]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576698669623087, 360576703367619539⟩, ⟨158163211536287944, 158252278436025714⟩, true⟩

def words02 : List Nat := [360582354952935039, 360582354953304372, 360582354541865366, 360582353492108152, 360582352442366450, 360582350624735424, 360582349588859511, 360582349706031510, 360582349706360593, 360582349185615830]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591286019534862, 360591290721014376⟩, ⟨(-250757005412496374), (-250667840864940306)⟩, true⟩

def words03 : List Nat := [360582350052455792, 360582351120740909, 360582352382525395, 360582352772160124, 360582352772509668, 360582351947279872, 360582351122038721, 360582350749545455, 360582351068675477, 360582351387864170]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573030834900935, 360573035539905535⟩, ⟨261025856297220662, 261115119704888766⟩, true⟩

def words04 : List Nat := [360582351388194893, 360582350897405028, 360582350673143501, 360582350891948951, 360582350892258355, 360582350535460881, 360582349502164451, 360582347831767351, 360582346161423899, 360582344456829061]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280A
