import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284A

def state06 : KState := ⟨⟨360599669026235511, 360599673875790688⟩, ⟨(-495611895143215937), (-495518547383783527)⟩, true⟩

def words05 : List Nat := [360582263383486841, 360582263743370054, 360582264798162805, 360582265197650390, 360582265198002435, 360582264430784795, 360582263663552831, 360582262492972638, 360582262823139890, 360582263435279681]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606339672314345, 360606344525450198⟩, ⟨(-685538317040796032), (-685444867357690362)⟩, true⟩

def words06 : List Nat := [360582263435614450, 360582263706305137, 360582265308955992, 360582266911604030, 360582268201243320, 360582268780536653, 360582268780874472, 360582268730099509, 360582268679259250, 360582269330783426]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564171866913016, 360564176723586079⟩, ⟨515327778486542563, 515421328891794787⟩, true⟩

def words07 : List Nat := [360582271029642508, 360582272728454042, 360582273812508373, 360582274349684851, 360582274350000589, 360582274061938677, 360582274713822906, 360582275017354068, 360582275017691100, 360582274382606157]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600890264253285, 360600895124478676⟩, ⟨(-530770806664888150), (-530677155072134668)⟩, true⟩

def words08 : List Nat := [360582273747481620, 360582274314242662, 360582274452646952, 360582274591106737, 360582274591456765, 360582273662422138, 360582271508320576, 360582270210565570, 360582268912792019, 360582268991486780]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587947025071689, 360587951888875733⟩, ⟨(-161910523689746296), (-161816770123624394)⟩, true⟩

def words09 : List Nat := [360582269031825565, 360582269072203579, 360582270339519863, 360582272226079191, 360582273481839784, 360582274737575229, 360582274934574892, 360582274934951077, 360582274107037927, 360582274306681297]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284B
