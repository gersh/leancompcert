import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293A

def state06 : KState := ⟨⟨360637638700321958, 360637643875239929⟩, ⟨(-1596339681595709351), (-1596236926791644927)⟩, true⟩

def words05 : List Nat := [360583264485225399, 360583265612374436, 360583267608644480, 360583269267990800, 360583269950235470, 360583270632463520, 360583271995183299, 360583274279957088, 360583276132099766, 360583277984201081]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608183432212697, 360608188610827553⟩, ⟨(-731628027624772729), (-731525164261628413)⟩, true⟩

def words06 : List Nat := [360583279257184968, 360583279784614757, 360583281468717592, 360583283152819272, 360583284027168696, 360583284027557363, 360583283748858573, 360583282718170416, 360583281687478365, 360583282235005769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552437497909265, 360552442680190245⟩, ⟨906047873346195656, 906150844401836092⟩, true⟩

def words07 : List Nat := [360583283606105396, 360583284977192173, 360583285770087115, 360583286077883782, 360583286078209697, 360583285952328831, 360583286307339147, 360583286307728169, 360583286168141713, 360583285118733535]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360661221371804886, 360661226557752159⟩, ⟨(-2290663105865164655), (-2290560027075192711)⟩, true⟩

def words08 : List Nat := [360583284069309255, 360583283187204458, 360583284009489920, 360583284998321200, 360583285015348327, 360583285067641002, 360583286274650653, 360583287481692219, 360583289843260744, 360583292495383571]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604642516659828, 360604647706318786⟩, ⟨(-627639095371235363), (-627535907477049737)⟩, true⟩

def words09 : List Nat := [360583294380451538, 360583296265436261, 360583297215655537, 360583298979543303, 360583300452721345, 360583301925862597, 360583302648369512, 360583302648758693, 360583302947109522, 360583303673548573]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293B
