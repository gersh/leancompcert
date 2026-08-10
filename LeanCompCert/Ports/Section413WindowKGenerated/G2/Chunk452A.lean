import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607396506127230, 360607409217082992⟩, ⟨(-1093821722870703249), (-1093433470856602549)⟩, true⟩

def state01 : KState := ⟨⟨360604615682890912, 360604628399737534⟩, ⟨(-968359959921761274), (-967971441611476544)⟩, true⟩

def words00 : List Nat := [360583218918838871, 360583218919457670, 360583218768922616, 360583218774566225, 360583218775084188, 360583218656363969, 360583218553747470, 360583218205759481, 360583217857668661, 360583218312776143]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593538113853993, 360593550836536941⟩, ⟨(-467429224856231791), (-467040442657057447)⟩, true⟩

def words01 : List Nat := [360583219049333763, 360583219785976888, 360583220146347572, 360583220598644286, 360583220926691689, 360583221254894731, 360583221949037371, 360583222423763418, 360583222652718541, 360583222881766878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586834432271380, 360586847160792403⟩, ⟨(-164218292060609592), (-163829245834532032)⟩, true⟩

def words02 : List Nat := [360583223185861315, 360583223736112631, 360583224575154719, 360583225414277988, 360583225817105016, 360583225817724117, 360583225733080860, 360583225400293235, 360583225067339374, 360583225104109276]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579451043944143, 360579463778362946⟩, ⟨169844199004348752, 170233512015748612⟩, true⟩

def words03 : List Nat := [360583225104660862, 360583224939921446, 360583225097701523, 360583225803632305, 360583226333305766, 360583226863056949, 360583227054303935, 360583227054923197, 360583226758974789, 360583226676506531]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556124998505155, 360556137738758818⟩, ⟨1225059269313684286, 1225448846324263388⟩, true⟩

def words04 : List Nat := [360583226593842211, 360583226349940684, 360583225618898538, 360583224516148273, 360583223413345841, 360583222186865432, 360583221205845112, 360583220712712426, 360583220219523304, 360583219481219023]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452A
