import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554963076745381, 360554999025968463⟩, ⟨2032673719472885119, 2034482662245847531⟩, true⟩

def state01 : KState := ⟨⟨360558163391547238, 360558199350787049⟩, ⟨1794142576110460248, 1795952265180445150⟩, true⟩

def words00 : List Nat := [360582307152399836, 360582306727273448, 360582306391588101, 360582305996418642, 360582305601177303, 360582305052491059, 360582304323635639, 360582303775004280, 360582303226056297, 360582302857231560]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561941145723093, 360561977115069791⟩, ⟨1512616716593363534, 1514427158775168572⟩, true⟩

def words01 : List Nat := [360582302534698344, 360582302088002338, 360582301641115372, 360582301342026467, 360582301177190223, 360582300888546126, 360582300599789441, 360582300200206258, 360582299812201944, 360582299540710897]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575568317747270, 360575604297093161⟩, ⟨497070725367776080, 498881912738776202⟩, true⟩

def words02 : List Nat := [360582299268860785, 360582299177052252, 360582299090579346, 360582298914191800, 360582298737642351, 360582298439586160, 360582298231987081, 360582298204384562, 360582298176694699, 360582298003154328]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603058599855262, 360603094589203792⟩, ⟨(-1551935864655905316), (-1550123931738297214)⟩, true⟩

def words03 : List Nat := [360582298004162504, 360582298095290497, 360582298320523930, 360582298410946746, 360582298411924786, 360582298349028506, 360582298301422829, 360582298441180911, 360582298721031465, 360582299001114844]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584492744533365, 360584528743998008⟩, ⟨(-168048539967053461), (-166235852946425971)⟩, true⟩

def words04 : List Nat := [360582299191053790, 360582299395779485, 360582299542525270, 360582299689562197, 360582299729238126, 360582299730298778, 360582299590248762, 360582299309276685, 360582299028109091, 360582298916726122]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360556740206207398, 360556776215656576⟩, ⟨1901107699659716372, 1902921131078392598⟩, true⟩

def words05 : List Nat := [360582299127160611, 360582299337792598, 360582299458356770, 360582299459417475, 360582299400159424, 360582299200699890, 360582299000935932, 360582298797341849, 360582298567742850, 360582298226534774]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592491189937655, 360592527209398807⟩, ⟨(-764605440030270818), (-762791262068654694)⟩, true⟩

def words06 : List Nat := [360582297885095464, 360582297723596240, 360582297817386744, 360582297938018983, 360582297939006647, 360582297907722287, 360582297854929860, 360582297919072848, 360582298010740317, 360582298149012482]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587033263385759, 360587069292966590⟩, ⟨(-357578093256276535), (-355763160622266543)⟩, true⟩

def words07 : List Nat := [360582298149974719, 360582298133096809, 360582298277633623, 360582298532620523, 360582298693740132, 360582298855025775, 360582298926326123, 360582299004873544, 360582299069696254, 360582299134875089]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580496619357180, 360580532658917019⟩, ⟨129915487645636138, 131731164565297820⟩, true⟩

def words08 : List Nat := [360582299253138236, 360582299254199496, 360582299243000245, 360582299141288568, 360582299039422155, 360582298814209744, 360582298742410655, 360582298796890938, 360582298797838207, 360582298728960796]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603152111679530, 360603188161275607⟩, ⟨(-1560087307885858313), (-1558270882313427791)⟩, true⟩

def words09 : List Nat := [360582298710339802, 360582298715733062, 360582298851849441, 360582299020054593, 360582299035059415, 360582299050149191, 360582299244475863, 360582299529665183, 360582299810546764, 360582300091647675]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745
