import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614662549343210, 360614685231059728⟩, ⟨(-1944976971976457501), (-1944062171004219241)⟩, true⟩

def state01 : KState := ⟨⟨360621410281860115, 360621432971452024⟩, ⟨(-2347933825012857737), (-2347018553840061161)⟩, true⟩

def words00 : List Nat := [360582122685429103, 360582123170539588, 360582123441646748, 360582123712825545, 360582123912084920, 360582124270823239, 360582124909969548, 360582125549261543, 360582126011037573, 360582126670203677]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617643059276201, 360617665756739850⟩, ⟨(-2122947076347506624), (-2122031335113366106)⟩, true⟩

def words01 : List Nat := [360582127425942548, 360582128181900595, 360582129169133849, 360582129955927016, 360582130504913245, 360582131053939195, 360582131508857076, 360582132150561883, 360582132746245142, 360582133342093187]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360620053227936224, 360620075933355238⟩, ⟨(-2267033668272599466), (-2266117451905611340)⟩, true⟩

def words02 : List Nat := [360582133742748357, 360582134061989952, 360582134661610204, 360582135261481204, 360582135790182360, 360582136039810742, 360582136126737259, 360582136213751987, 360582136581116985, 360582137217246256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579159413754615, 360579182127047137⟩, ⟨175703106944324960, 176619793634939940⟩, true⟩

def words03 : List Nat := [360582137731629383, 360582138246142502, 360582138620033129, 360582138714871699, 360582138715573971, 360582138656456469, 360582138597094716, 360582138649544452, 360582138650288584, 360582138601664395]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608931078622815, 360608953799797007⟩, ⟨(-1603030356424255596), (-1602113198843339842)⟩, true⟩

def words04 : List Nat := [360582138552856086, 360582138682071434, 360582139099164031, 360582139516402941, 360582139662416895, 360582139663252598, 360582139676649349, 360582139824111626, 360582140188908453, 360582140638530362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597A
