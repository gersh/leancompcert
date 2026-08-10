import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374A

def state06 : KState := ⟨⟨360575527861094629, 360575536458563513⟩, ⟨224918071935010071, 225135775112433745⟩, true⟩

def words05 : List Nat := [360581549937220003, 360581550237675524, 360581550459942714, 360581550460447677, 360581550218960211, 360581549246788368, 360581548274578863, 360581547281011771, 360581546649853610, 360581546489933306]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584462653856325, 360584471256134788⟩, ⟨(-110071462772287856), (-109853579404587276)⟩, true⟩

def words06 : List Nat := [360581546329948791, 360581545811116727, 360581544582111504, 360581544065117416, 360581543548007923, 360581542689755279, 360581542100794914, 360581541055579843, 360581540010321109, 360581539560172455]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360528381888701280, 360528390495742022⟩, ⟨1991541490273459655, 1991759552107766773⟩, true⟩

def words07 : List Nat := [360581539560588114, 360581539427362178, 360581539294088170, 360581538802342974, 360581537911556663, 360581536837005543, 360581535762360961, 360581534790944282, 360581533843550410, 360581532426161120]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582535542898424, 360582544154705305⟩, ⟨(-38434642673933488), (-38216402181290246)⟩, true⟩

def words08 : List Nat := [360581531008733369, 360581529992616819, 360581529385626472, 360581529437943236, 360581529438422793, 360581528750213877, 360581527352760340, 360581526257860245, 360581525162866856, 360581524806003449]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545475147067500, 360545483763691351⟩, ⟨1351325836773716856, 1351544257878328450⟩, true⟩

def words09 : List Nat := [360581524806453554, 360581524476106641, 360581524525465773, 360581525266962453, 360581525825595047, 360581526384280582, 360581526498564675, 360581526499070146, 360581525904448399, 360581524943901440]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374B
