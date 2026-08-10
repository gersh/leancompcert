import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343A

def state06 : KState := ⟨⟨360583150135871302, 360583157318166017⟩, ⟨(-56086666571450203), (-55919816271742613)⟩, true⟩

def words05 : List Nat := [360581520015732143, 360581522618378030, 360581524553589085, 360581525903280375, 360581527038605468, 360581528173994842, 360581529217785430, 360581529801452030, 360581529849230314, 360581529897070248]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653817611887080, 360653824798528409⟩, ⟨(-2484648740894532664), (-2484481741223555878)⟩, true⟩

def words06 : List Nat := [360581530790729080, 360581532236072310, 360581533654429596, 360581535072789110, 360581535746690673, 360581535747150916, 360581536253390668, 360581536929600476, 360581538451194272, 360581540554798999]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619016665271079, 360619023856298729⟩, ⟨(-1288330179938896026), (-1288163029488801686)⟩, true⟩

def words07 : List Nat := [360581542087116058, 360581543619391341, 360581545625526521, 360581548238470211, 360581550306732458, 360581552374946502, 360581553799922695, 360581554381895749, 360581555472130864, 360581556562459434]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360623898091879371, 360623905287240877⟩, ⟨(-1456260161304516976), (-1456092861834447204)⟩, true⟩

def words08 : List Nat := [360581558497521304, 360581559589692875, 360581560189914697, 360581560790159844, 360581560790547519, 360581561378158372, 360581562625489840, 360581563872836892, 360581564697585258, 360581565929215974]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628227661272318, 360628234860988283⟩, ⟨(-1605318928698573639), (-1605151479457704101)⟩, true⟩

def words09 : List Nat := [360581566815329031, 360581567701517927, 360581569217098941, 360581570313146064, 360581570688951334, 360581571064770922, 360581571251410104, 360581572123446495, 360581573480294078, 360581574837167531]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk343B
