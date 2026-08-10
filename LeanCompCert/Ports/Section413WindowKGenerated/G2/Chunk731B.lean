import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731A

def state06 : KState := ⟨⟨360609587217506212, 360609621835426033⟩, ⟨(-1989988919753963483), (-1988278269833993587)⟩, true⟩

def words05 : List Nat := [360582442782706500, 360582443051684785, 360582443471372867, 360582443753923460, 360582443876689872, 360582443999533666, 360582444115175025, 360582444339695577, 360582444712016485, 360582445084563771]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587495466510312, 360587530094344739⟩, ⟨(-373758668417177094), (-372047293098209376)⟩, true⟩

def words06 : List Nat := [360582445315163052, 360582445404627918, 360582445580724985, 360582445757146633, 360582445885941609, 360582445886981326, 360582445829320570, 360582445657849280, 360582445486182676, 360582445466649366]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559285739091497, 360559320376726028⟩, ⟨1690482500501861960, 1692194592945174100⟩, true⟩

def words07 : List Nat := [360582445532844077, 360582445599228387, 360582445600154894, 360582445573397602, 360582445359993964, 360582445100188378, 360582444840088950, 360582444628384837, 360582444422069368, 360582444107157091]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600238663650579, 360600273311102600⟩, ⟨(-1306694907938473661), (-1304982097003996695)⟩, true⟩

def words08 : List Nat := [360582443792017884, 360582443663644213, 360582443629055203, 360582443623290096, 360582443617464301, 360582443404574081, 360582443208575034, 360582443160719647, 360582443249944282, 360582443494636040]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587876438401103, 360587911095766538⟩, ⟨(-401788529522751039), (-400074992975800901)⟩, true⟩

def words09 : List Nat := [360582443634025098, 360582443773541081, 360582444041121375, 360582444448326672, 360582444807955993, 360582445167745951, 360582445433855695, 360582445513687762, 360582445589209946, 360582445665062371]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731B
