import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360655409416441142, 360655417985263959⟩, ⟨(-2763247963418080853), (-2763031332461579927)⟩, true⟩

def state01 : KState := ⟨⟨360636216583475076, 360636225157100644⟩, ⟨(-2045641742085121474), (-2045424931482147118)⟩, true⟩

def words00 : List Nat := [360581543499249790, 360581544168573574, 360581545387471605, 360581546606457215, 360581547641353023, 360581548224447354, 360581548334841216, 360581548445292758, 360581549269556971, 360581550731624658]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557034644805333, 360557043223176882⟩, ⟨916998943659794100, 917215931834281878⟩, true⟩

def words01 : List Nat := [360581552005326976, 360581553279054368, 360581554196741074, 360581554918250277, 360581555154382828, 360581555390628995, 360581555554340121, 360581555554844685, 360581555260171453, 360581554605641722]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591749801134967, 360591758384275993⟩, ⟨(-382088414379820955), (-381871247708539819)⟩, true⟩

def words02 : List Nat := [360581553951033430, 360581553976275200, 360581555034979253, 360581556093723330, 360581556542658049, 360581556543162549, 360581556280663290, 360581556229978562, 360581556179155885, 360581556379314637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558656123626108, 360558664711574976⟩, ⟨856777044118170281, 856994390771119891⟩, true⟩

def words03 : List Nat := [360581556379768197, 360581556297498477, 360581556215139524, 360581556235405555, 360581556316393120, 360581556397467597, 360581556397917077, 360581556119456967, 360581555129826993, 360581554519020786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584048774634406, 360584057367341464⟩, ⟨(-94134537766031437), (-93917012943058703)⟩, true⟩

def words04 : List Nat := [360581554009426164, 360581554009930921, 360581553639115692, 360581552723911864, 360581551808670218, 360581550710393304, 360581550003656900, 360581550006849164, 360581550007304352, 360581549636895200]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk374
