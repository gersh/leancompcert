import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474A

def state06 : KState := ⟨⟨360559657666768824, 360559671737131529⟩, ⟨1096559950741310952, 1097011197586769806⟩, true⟩

def words05 : List Nat := [360582791200595515, 360582790578175055, 360582789955665069, 360582789322916813, 360582789028929686, 360582788624390631, 360582788219802738, 360582787589837807, 360582786660785023, 360582786174501668]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360545596804249292, 360545610880755248⟩, ⟨1763936786360351268, 1764388324795487184⟩, true⟩

def words06 : List Nat := [360582785688010064, 360582785467176998, 360582785057042244, 360582784362620977, 360582783668124481, 360582782680873903, 360582781916656475, 360582781142261991, 360582780367828861, 360582779372956544]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597344937899331, 360597359020565127⟩, ⟨(-692869529924465779), (-692417699051650999)⟩, true⟩

def words07 : List Nat := [360582778590511980, 360582778062268621, 360582777533855458, 360582777248248655, 360582776977541263, 360582776322597616, 360582775667549097, 360582775372293742, 360582775664812535, 360582775972629076]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553728039538694, 360553742128429481⟩, ⟨1378113890769914234, 1378566017236450756⟩, true⟩

def words08 : List Nat := [360582775973223599, 360582775877437977, 360582775338989832, 360582775136595856, 360582774934030986, 360582774621148360, 360582773865707075, 360582772767500642, 360582771669206527, 360582770682172089]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360539355257117088, 360539369352153313⟩, ⟨2060779159042945069, 2061231577386769921⟩, true⟩

def words09 : List Nat := [360582770071456748, 360582769902700828, 360582769733886090, 360582769344846623, 360582768513311411, 360582767276771390, 360582766040092103, 360582765245298480, 360582764614057169, 360582763701150930]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk474B
