import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664A

def state06 : KState := ⟨⟨362460988525069619, 362461053810348550⟩, ⟨1622321691065766643, 1625252171152720695⟩, true⟩

def words05 : List Nat := [371285511334394022, 371285511139208845, 371285510943288714, 371285510719170212, 371285510213786699, 371285509779100542, 371285509343194280, 371285509134182138, 371285508767591379, 371285508402150427]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480667171213092, 362480732476777446⟩, ⟨314422883033030860, 317354711389392340⟩, true⟩

def words06 : List Nat := [371285508035734322, 371285507845048274, 371285507596898379, 371285507575777085, 371285507553964243, 371285507474877320, 371285507119154272, 371285506990643339, 371285506879587482, 371285506881943527]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474124426799928, 362474189753051993⟩, ⟨749385676287107049, 752318879861664605⟩, true⟩

def words07 : List Nat := [371285506811811177, 371285506742811852, 371285506717378971, 371285506719902424, 371285506652840735, 371285506653139859, 371285506652694470, 371285506653149717, 371285506389751018, 371285506222363992]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469450074393325, 362469515420830215⟩, ⟨1060192194415147536, 1063126739983718262⟩, true⟩

def words08 : List Nat := [371285506053683906, 371285506050877409, 371285505831148171, 371285505607852437, 371285505383699462, 371285505229960929, 371285504994280390, 371285504903027248, 371285504810992423, 371285504693502553]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483687368061897, 362483752735010335⟩, ⟨113467767092430803, 116403676574951679⟩, true⟩

def words09 : List Nat := [371285504454567838, 371285504442668102, 371285504457004058, 371285504459271433, 371285504187211808, 371285503882571941, 371285503576987854, 371285503440573821, 371285503189981288, 371285503166237027]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664B
