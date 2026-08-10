import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk244A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk244A
