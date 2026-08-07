import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk038

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361012621454753341, 361012621525640213⟩, ⟨(-1720603692751505000), (-1720603509769181686)⟩, true⟩

def state01 : KState := ⟨⟨360869248469412561, 360869248540697220⟩, ⟨(-1177210240823132679), (-1177210056327217625)⟩, true⟩

def words00 : List Nat := [360560016495387977, 360560016495429656, 360560081871837962, 360560148739814462, 360560197051303646, 360560240051838578, 360560244016430963, 360560247978946530, 360560269523241112, 360560350598863786]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360133418626491744, 360133418698170666⟩, ⟨1630740520748954382, 1630740706749023498⟩, true⟩

def words01 : List Nat := [360560460935459786, 360560571214189722, 360560636514325774, 360560636514367610, 360560634419735788, 360560584713839511, 360560535033975593, 360560491521393455, 360560425953102172, 360560314171141615]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360536810573732484, 360536810645808739⟩, ⟨89660981247077763, 89661168766862829⟩, true⟩

def words02 : List Nat := [360560202447681110, 360560170169382895, 360560249514933736, 360560328819004573, 360560342253303843, 360560342253345830, 360560288738081654, 360560267585143224, 360560246443241870, 360560220872640819]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360457182794841896, 360457182867319176⟩, ⟨395546398327709226, 395546587385472930⟩, true⟩

def words03 : List Nat := [360560214761943109, 360560173722915968, 360560159032425916, 360560224337934161, 360560244454788019, 360560264561163435, 360560264561201073, 360560249894041000, 360560216622776796, 360560189791117477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360702556103934827, 360702556176810772⟩, ⟨(-549444037998442508), (-549443847407827794)⟩, true⟩

def words04 : List Nat := [360560162973415872, 360560161137211913, 360560142809524258, 360560069479995039, 360559996188601877, 360559904764830438, 360559857896808530, 360559867859959202, 360559867859996961, 360559880547777319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360959340952583774, 360959341025859145⟩, ⟨(-1538275279566655628), (-1538275087436224734)⟩, true⟩

def words05 : List Nat := [360559984232423591, 360560087863262123, 360560258051352880, 360560404290962745, 360560492625458414, 360560580914152602, 360560633884386085, 360560720894286512, 360560824163785206, 360560927379799517]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653139814818063, 360653139888498254⟩, ⟨(-357050711984001764), (-357050518288965326)⟩, true⟩

def words06 : List Nat := [360560975185268030, 360560975185310450, 360561006252743984, 360561054925016473, 360561085542664218, 360561085542706676, 360561050799876935, 360560982029565700, 360560913294795970, 360560902606584288]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360476230913611776, 360476230987693528⟩, ⟨328003475472983105, 328003670724094207⟩, true⟩

def words07 : List Nat := [360560917690704212, 360560932767042405, 360560932767080400, 360560914023705151, 360560883127712893, 360560825837801749, 360560777107846528, 360560789809659173, 360560789809697523, 360560768016230666]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360842614623698543, 360842614698183087⟩, ⟨(-1095173585509342052), (-1095173388693351098)⟩, true⟩

def words08 : List Nat := [360560790122969672, 360560867317239577, 360560951104911150, 360561034849456559, 360561051922285645, 360561051922328384, 360561046592504793, 360561035638592501, 360561079122639365, 360561151478267037]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360431740572764398, 360431740647657384⟩, ⟨506086163158941366, 506086361565818426⟩, true⟩

def words09 : List Nat := [360561190341448911, 360561229184670380, 360561284651305434, 360561395300523965, 360561464463125283, 360561533590238096, 360561568684064182, 360561568684107022, 360561539663142153, 360561506381392210]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk038
