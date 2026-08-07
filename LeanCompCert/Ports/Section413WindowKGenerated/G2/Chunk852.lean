import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564828593355462, 360564876106438761⟩, ⟨1490935290538231703, 1493669087312143277⟩, true⟩

def state01 : KState := ⟨⟨360584259454009314, 360584306978618831⟩, ⟨(-164653373274920887), (-161918594408420013)⟩, true⟩

def words00 : List Nat := [360582407228979928, 360582407162087332, 360582407106804152, 360582406983029924, 360582406859034090, 360582406700718052, 360582406702463849, 360582406759548327, 360582406760639068, 360582406770964791]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586647392405089, 360586694928592217⟩, ⟨(-368199266285976109), (-365463500836156137)⟩, true⟩

def words01 : List Nat := [360582406771972930, 360582406741090141, 360582406815181564, 360582406817180139, 360582406818318879, 360582406697890892, 360582406577238010, 360582406438655794, 360582406456298381, 360582406507887976]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578671017732738, 360578718565588635⟩, ⟨311462409700795345, 314199169620067269⟩, true⟩

def words02 : List Nat := [360582406508992284, 360582406460973871, 360582406275061356, 360582406227077661, 360582406178788888, 360582406035913584, 360582405807050776, 360582405509274634, 360582405211256520, 360582405051211304]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572728833708650, 360572776393112816⟩, ⟨817971458794177677, 820709203029276521⟩, true⟩

def words03 : List Nat := [360582405041148958, 360582405074593962, 360582405075685100, 360582405040063366, 360582404945035980, 360582404815724199, 360582404692915072, 360582404720505751, 360582404721635507, 360582404609947979]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610181689398786, 360610229260362087⟩, ⟨(-2374759217961850366), (-2372020488367966508)⟩, true⟩

def words04 : List Nat := [360582404497990136, 360582404387878326, 360582404441915198, 360582404538412648, 360582404539542332, 360582404518930950, 360582404621290889, 360582404742083491, 360582404971829235, 360582405299489277]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852
