import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360559793588468568, 360559822152176882⟩, ⟨1539964996835175146, 1541251951176603020⟩, true⟩

def state01 : KState := ⟨⟨360574156763067093, 360574185335672441⟩, ⟨581857650087065946, 583145197905032606⟩, true⟩

def words00 : List Nat := [360582929032162612, 360582928911070062, 360582928902491712, 360582928799775311, 360582928696982543, 360582928402566890, 360582927883683355, 360582927500482960, 360582927117007130, 360582926831668619]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561987333660623, 360562015915222598⟩, ⟨1393759099357389889, 1395047244717301075⟩, true⟩

def words01 : List Nat := [360582926701472409, 360582926422784227, 360582926143923497, 360582926146877137, 360582926147670306, 360582926057905377, 360582925968059436, 360582925700742103, 360582925209023235, 360582924896708170]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561260954251418, 360561289544682271⟩, ⟨1442228993000119022, 1443517730135080518⟩, true⟩

def words02 : List Nat := [360582924584090008, 360582924495830807, 360582924245545833, 360582923849934412, 360582923454168076, 360582922917401313, 360582922555112256, 360582922347788907, 360582922140372094, 360582921760029718]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582449329855281, 360582477929179139⟩, ⟨28139915105229102, 29429245714487312⟩, true⟩

def words03 : List Nat := [360582921436633926, 360582921108675688, 360582920780450883, 360582920676499583, 360582920422014357, 360582919975931957, 360582919529687411, 360582919118344024, 360582918888447870, 360582918882815856]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589201853115255, 360589230461409387⟩, ⟨(-422658847639514891), (-421368918311511381)⟩, true⟩

def words04 : List Nat := [360582918877047956, 360582918759315043, 360582918762324936, 360582918832577172, 360582918833379115, 360582918748798532, 360582918562800727, 360582918240030220, 360582917917081883, 360582917913008442]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667A
