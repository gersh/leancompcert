import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk244

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582652473965293, 360582655991117394⟩, ⟨14019473528461540, 14077531204580804⟩, true⟩

def state01 : KState := ⟨⟨360598914963729487, 360598918483888126⟩, ⟨(-382695441487455477), (-382637310436797121)⟩, true⟩

def words00 : List Nat := [360583233372664608, 360583235111841892, 360583237612007429, 360583240112028386, 360583241202413875, 360583241202732038, 360583241728629700, 360583242830351988, 360583243050931415, 360583243693406917]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622177744935467, 360622181268125195⟩, ⟨(-950706472958390601), (-950648267904194381)⟩, true⟩

def words01 : List Nat := [360583243693690558, 360583243347841151, 360583244332600936, 360583246743312403, 360583248331803940, 360583249920222039, 360583250669440795, 360583250669759427, 360583252182260302, 360583253776707801]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622412935400064, 360622416461591662⟩, ⟨(-956559614890129758), (-956501336515300470)⟩, true⟩

def words02 : List Nat := [360583257046956072, 360583258653385965, 360583258973654609, 360583259293927062, 360583259294194036, 360583260236488385, 360583261782005237, 360583263327455329, 360583263725418806, 360583265328338202]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360663936343263641, 360663939872460053⟩, ⟨(-1971345875103099722), (-1971287523305650106)⟩, true⟩

def words03 : List Nat := [360583267165699557, 360583269003001681, 360583271952493019, 360583274206181041, 360583275055962372, 360583275905696267, 360583276698359257, 360583278325845902, 360583281626494376, 360583284926946136]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360690121137725595, 360690124669955686⟩, ⟨(-2611624428759531603), (-2611566002804090693)⟩, true⟩

def words04 : List Nat := [360583287380593315, 360583289840385475, 360583293972788010, 360583298104954557, 360583301800038606, 360583304965113615, 360583307108041931, 360583309250829470, 360583312154140175, 360583316522934947]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595619237241543, 360595622772476766⟩, ⟨(-300654599745080681), (-300596100298993641)⟩, true⟩

def words05 : List Nat := [360583320814589192, 360583325105948696, 360583327972965000, 360583329180764865, 360583329645906881, 360583330111094813, 360583331522018893, 360583332976682851, 360583333479411834, 360583333982145259]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360682838202436419, 360682841740681844⟩, ⟨(-2434516711377770809), (-2434458138287091183)⟩, true⟩

def words06 : List Nat := [360583335608499960, 360583338138313817, 360583341195173957, 360583344251846407, 360583345694642700, 360583346674121580, 360583348653464144, 360583350632737817, 360583354280675125, 360583358346530110]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611189566090246, 360611193107381890⟩, ⟨(-680652784575355233), (-680594136928590005)⟩, true⟩

def words07 : List Nat := [360583361580283564, 360583364813811437, 360583369715517047, 360583375447914924, 360583379984411636, 360583384520587725, 360583388049435820, 360583389922922017, 360583391058936978, 360583392194962929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360634266323699378, 360634269867995636⟩, ⟨(-1245792131816221419), (-1245733410601486603)⟩, true⟩

def words08 : List Nat := [360583394998551728, 360583396147132323, 360583396450968377, 360583396754814345, 360583396755081811, 360583397321988501, 360583399449116249, 360583401576131071, 360583402843957281, 360583404921255957]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360636421620601263, 360636425167918105⟩, ⟨(-1298737393379668663), (-1298678598176190059)⟩, true⟩

def words09 : List Nat := [360583407702645118, 360583410483901351, 360583413208022392, 360583415070316396, 360583415320137451, 360583415569962656, 360583415570223681, 360583415713950087, 360583417877859909, 360583420041671169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk244
