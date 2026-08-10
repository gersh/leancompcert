import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601A

def state06 : KState := ⟨⟨360599037864420810, 360599060911041880⟩, ⟨(-1011154559480864702), (-1010217889672505296)⟩, true⟩

def words05 : List Nat := [360582265178558924, 360582265868591339, 360582266419578581, 360582266850907717, 360582267161849069, 360582267473012577, 360582267955747261, 360582268444618949, 360582268724503985, 360582269004496569]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360649537231665520, 360649560286231383⟩, ⟨(-4049483399116408088), (-4048546251310599794)⟩, true⟩

def words06 : List Nat := [360582269560695565, 360582270299425875, 360582271130212130, 360582271961134450, 360582272530954202, 360582272910875386, 360582273566974665, 360582274223300665, 360582275155699431, 360582276274808761]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360620099890860691, 360620122953453043⟩, ⟨(-2278033036644173768), (-2277095405845410998)⟩, true⟩

def words07 : List Nat := [360582277241555434, 360582278208376422, 360582279294066266, 360582280520784527, 360582281608547184, 360582282696409759, 360582283609269521, 360582284247168555, 360582284876620007, 360582285506321135]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620491553573709, 360620514624092713⟩, ⟨(-2301714037404285829), (-2300775929539054681)⟩, true⟩

def words08 : List Nat := [360582286177059128, 360582286572930955, 360582286829591610, 360582287086328111, 360582287272248108, 360582287675523909, 360582288297980025, 360582288920577307, 360582289404251095, 360582290040192478]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360622035852043395, 360622058930524960⟩, ⟨(-2394739651339732673), (-2393801064169056913)⟩, true⟩

def words09 : List Nat := [360582290803054229, 360582291566153829, 360582292320802739, 360582292800640595, 360582293046640110, 360582293292697412, 360582293630991453, 360582294131131659, 360582294792357851, 360582295453769274]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601B
