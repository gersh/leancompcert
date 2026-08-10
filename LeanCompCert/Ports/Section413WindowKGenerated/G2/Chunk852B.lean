import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852A

def state06 : KState := ⟨⟨360596781876293098, 360596829458933686⟩, ⟨(-1232397759770932230), (-1229658034633104180)⟩, true⟩

def words05 : List Nat := [360582405550154761, 360582405800948058, 360582406005094419, 360582406295451634, 360582406488088670, 360582406680918113, 360582406805047182, 360582406837973571, 360582407008124317, 360582407178704354]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572493760421286, 360572541354590758⟩, ⟨838491182018935892, 841231890168057072⟩, true⟩

def words06 : List Nat := [360582407314506814, 360582407347738287, 360582407348829877, 360582407300124939, 360582407251221080, 360582407168055083, 360582407154071793, 360582407083468614, 360582407012733833, 360582406862860584]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605364738310783, 360605412344049427⟩, ⟨(-1964603870601802121), (-1961862175893727981)⟩, true⟩

def words07 : List Nat := [360582406748155303, 360582406732679251, 360582406813607040, 360582406915366009, 360582406916508090, 360582406899283691, 360582406959491019, 360582407121554719, 360582407392306397, 360582407663336329]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572022028927316, 360572069646349695⟩, ⟨878938128563040683, 881680819717773075⟩, true⟩

def words08 : List Nat := [360582407826691881, 360582407852715753, 360582407899909081, 360582407947469238, 360582407948495450, 360582407931190513, 360582407776316968, 360582407552614540, 360582407328664740, 360582407092940360]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551895787100627, 360551943416058468⟩, ⟨2595635210518859242, 2598378885592302198⟩, true⟩

def words09 : List Nat := [360582406972731401, 360582406886495507, 360582406800144558, 360582406627523043, 360582406434024491, 360582406147265209, 360582405860152693, 360582405710618238, 360582405423552341, 360582405067706678]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852B
