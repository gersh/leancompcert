import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562724275933521, 360562738309270655⟩, ⟨951126990666460606, 951576481389041708⟩, true⟩

def state01 : KState := ⟨⟨360574970363725689, 360574984403194082⟩, ⟨370511893752396331, 370961675128010955⟩, true⟩

def words00 : List Nat := [360582813339467611, 360582813265669273, 360582812867907449, 360582812174416872, 360582811480839192, 360582810573855672, 360582809890004480, 360582809649771919, 360582809409478303, 360582808948124013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598587792837543, 360598601838463689⟩, ⟨(-749519893959510233), (-749069820614049965)⟩, true⟩

def words01 : List Nat := [360582808783626193, 360582808428842417, 360582808073876728, 360582807870447613, 360582807349960729, 360582806458422105, 360582805566796273, 360582805118680397, 360582805342204418, 360582805675991071]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579654191019599, 360579668242860540⟩, ⟨148202769525109428, 148653137605627924⟩, true⟩

def words02 : List Nat := [360582805677995371, 360582805678647442, 360582805351798252, 360582805323188713, 360582805294412975, 360582804953131848, 360582804409750468, 360582803645589105, 360582802881335212, 360582802401359500]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360526030816452775, 360526044874441683⟩, ⟨2692007434840603766, 2692458094549235470⟩, true⟩

def words03 : List Nat := [360582802712727028, 360582803090297718, 360582803177531977, 360582803178184489, 360582803019229425, 360582802674645485, 360582802329887475, 360582801931167947, 360582801089001924, 360582799893298118]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360563684717354992, 360563698781501639⟩, ⟨905503398984726870, 905954350847062936⟩, true⟩

def words04 : List Nat := [360582798697497026, 360582797944809433, 360582797414903419, 360582796754697664, 360582796094468281, 360582795052052009, 360582794024782099, 360582793149169422, 360582792273396594, 360582791602383559]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474A
