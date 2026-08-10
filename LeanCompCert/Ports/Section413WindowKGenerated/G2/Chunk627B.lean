import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627A

def state06 : KState := ⟨⟨360579328360031179, 360579353526115557⟩, ⟨206732133736882689, 207799086753765889⟩, true⟩

def words05 : List Nat := [360582663713924098, 360582663751023687, 360582664041651875, 360582664459158490, 360582664634420082, 360582664809802750, 360582664825748317, 360582664826629525, 360582664589448067, 360582664537695445]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594232562765949, 360594257737162850⟩, ⟨(-728677083534347037), (-727609608782046611)⟩, true⟩

def words06 : List Nat := [360582664686527071, 360582664895005129, 360582664975677717, 360582665056450630, 360582665072936896, 360582665281597500, 360582665609262582, 360582665937085023, 360582666058557759, 360582666244136102]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604419916611312, 360604445099325031⟩, ⟨(-1368193491287903942), (-1367125494448423318)⟩, true⟩

def words07 : List Nat := [360582666578960351, 360582666914032173, 360582667502346753, 360582667837906824, 360582667963784655, 360582668089734607, 360582668132219196, 360582668301406983, 360582668648994462, 360582668996770940]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570279983827868, 360570305174951037⟩, ⟨775107371568922432, 776175896393640564⟩, true⟩

def words08 : List Nat := [360582669167579086, 360582669168460574, 360582669086356855, 360582668997932928, 360582668909269915, 360582668703099931, 360582668244012220, 360582667657464857, 360582667070761840, 360582666632132016]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360537191934348495, 360537217133765954⟩, ⟨2852968293927862334, 2854037339593851146⟩, true⟩

def words09 : List Nat := [360582666492482483, 360582666549867062, 360582666550659786, 360582666481910667, 360582666160233751, 360582665722146402, 360582665283826790, 360582664839155290, 360582664310985479, 360582663588218086]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627B
