import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607291007985102, 360607322121686057⟩, ⟨(-1713305585920470971), (-1711844950799342911)⟩, true⟩

def state01 : KState := ⟨⟨360594909545081208, 360594940668158421⟩, ⟨(-852798986733457686), (-851337699915628620)⟩, true⟩

def words00 : List Nat := [360582691865461316, 360582692129087794, 360582692388654173, 360582692648487735, 360582692856265924, 360582692969458961, 360582692978821362, 360582692988282438, 360582692989083478, 360582693143307454]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547671977625339, 360547703109963736⟩, ⟨2430971410172921761, 2432433340783164443⟩, true⟩

def words01 : List Nat := [360582693381217698, 360582693619305632, 360582693689155090, 360582693690139023, 360582693553149388, 360582693364695125, 360582693175961509, 360582692983588233, 360582692584344665, 360582692082069363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569851754694647, 360569882896317686⟩, ⟨888906184401767949, 890368760526201347⟩, true⟩

def words02 : List Nat := [360582691579580408, 360582691168705623, 360582690861890211, 360582690675638675, 360582690489304704, 360582690121883072, 360582689547559629, 360582689142597475, 360582688737359541, 360582688430051703]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573580644381620, 360573611795390978⟩, ⟨629544109245904265, 631007338046880123⟩, true⟩

def words03 : List Nat := [360582688246780400, 360582687858604516, 360582687470252085, 360582687206821236, 360582687046373093, 360582686834442875, 360582686622415119, 360582686280544056, 360582685944570623, 360582685815207586]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584276827396847, 360584307987671616⟩, ⟨(-114303589958092770), (-112839716794099128)⟩, true⟩

def words04 : List Nat := [360582685726188366, 360582685813282632, 360582685814167911, 360582685797673018, 360582685781032642, 360582685620046541, 360582685619267703, 360582685654927989, 360582685655805244, 360582685585164189]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk695A
