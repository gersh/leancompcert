import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708A

def state06 : KState := ⟨⟨360559823270621482, 360559855663833563⟩, ⟨1595751865652252677, 1597302299811819053⟩, true⟩

def words05 : List Nat := [360582400158621153, 360582399688128340, 360582399217456606, 360582398945851771, 360582398830419358, 360582398618876507, 360582398407235965, 360582398095724003, 360582397644649648, 360582397327675108]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562177293407786, 360562209696092696⟩, ⟨1428848750065621851, 1430399855516961505⟩, true⟩

def words06 : List Nat := [360582397010390513, 360582396643217715, 360582396246980139, 360582395699167181, 360582395151205588, 360582394553409467, 360582394072900681, 360582393791277176, 360582393509534823, 360582393128511449]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576286345166240, 360576318757330298⟩, ⟨428783689682885787, 430335466967188977⟩, true⟩

def words07 : List Nat := [360582392844532552, 360582392716251019, 360582392587686172, 360582392392381381, 360582391998237867, 360582391415877389, 360582390833335117, 360582390449710606, 360582390166256269, 360582390081638526]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571776890716514, 360571809312464447⟩, ⟨748431958811759968, 749984415446765824⟩, true⟩

def words08 : List Nat := [360582389996878549, 360582389812854920, 360582389692328193, 360582389706603259, 360582389707444169, 360582389671527388, 360582389582079198, 360582389393391057, 360582389204536245, 360582388864100035]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360542825406426736, 360542857837629390⟩, ⟨2801028220042863355, 2802581346971716707⟩, true⟩

def words09 : List Nat := [360582388764959488, 360582388815247310, 360582388816151080, 360582388766561499, 360582388518128281, 360582388139662786, 360582387760894572, 360582387502334595, 360582387044996717, 360582386488503463]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708B
