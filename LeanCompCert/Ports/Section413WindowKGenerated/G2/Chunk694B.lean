import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694A

def state06 : KState := ⟨⟨360553175848771444, 360553206925250991⟩, ⟨2046855681978539212, 2048313730959753972⟩, true⟩

def words05 : List Nat := [360582698387264301, 360582698154893923, 360582697922431273, 360582697586224730, 360582697395515372, 360582697110395432, 360582696824995429, 360582696746582106, 360582696460950890, 360582696037415687]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583366122234083, 360583397208005088⟩, ⟨(-50334646256943911), (-48875951844772059)⟩, true⟩

def words06 : List Nat := [360582695613682441, 360582695186350499, 360582694912522317, 360582694845647612, 360582694778702625, 360582694507187121, 360582694098383360, 360582693896632627, 360582693694580599, 360582693663334006]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564256095902255, 360564287191042532⟩, ⟨1277398134555033727, 1278857479897082961⟩, true⟩

def words07 : List Nat := [360582693664219876, 360582693557234401, 360582693548790413, 360582693753081311, 360582693812618662, 360582693872305821, 360582693873181952, 360582693829473977, 360582693578602080, 360582693314817678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565121590170472, 360565152694584415⟩, ⟨1217308756208017441, 1218768745930474927⟩, true⟩

def words08 : List Nat := [360582693050704051, 360582692993461421, 360582692945126797, 360582692745328493, 360582692545378858, 360582692232895250, 360582692054516975, 360582691908755192, 360582691762913673, 360582691459096295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607291007985102, 360607322121686057⟩, ⟨(-1713305585920470971), (-1711844950799342911)⟩, true⟩

def words09 : List Nat := [360582691207502563, 360582691162803943, 360582691278631959, 360582691279615475, 360582691234437470, 360582691005802271, 360582690776965493, 360582690902863789, 360582691258065193, 360582691613480430]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694B
