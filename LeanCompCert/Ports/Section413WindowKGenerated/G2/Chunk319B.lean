import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319A

def state06 : KState := ⟨⟨360468111444295239, 360468117620961672⟩, ⟨3643816745296073452, 3643950233264410468⟩, true⟩

def words05 : List Nat := [360582160413222938, 360582158255345775, 360582156097557334, 360582153452178842, 360582150535256363, 360582146728618226, 360582142922093956, 360582140090143058, 360582137152835339, 360582133585707117]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360537119102431715, 360537125283121573⟩, ⟨1438095949170640187, 1438229565747788839⟩, true⟩

def words06 : List Nat := [360582130018705062, 360582127035829971, 360582124803630424, 360582123545540805, 360582122287496623, 360582120190708333, 360582117963299017, 360582116027409291, 360582114091517220, 360582112132222224]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360537679320855840, 360537685505599334⟩, ⟨1420215314806076949, 1420349060997804075⟩, true⟩

def words07 : List Nat := [360582110725487333, 360582108831892010, 360582106938333816, 360582106018241581, 360582105621498133, 360582104961391510, 360582104301280327, 360582102729810152, 360582100560648050, 360582099172297202]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360543852778078420, 360543858966835270⟩, ⟨1222645010658550414, 1222778885218219792⟩, true⟩

def words08 : List Nat := [360582097783890003, 360582097368387891, 360582095976879353, 360582093826709045, 360582091676603831, 360582089283931539, 360582087377933996, 360582085998023656, 360582084618150433, 360582082751931182]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552125222440603, 360552131415217405⟩, ⟨958006651254006128, 958140654431876222⟩, true⟩

def words09 : List Nat := [360582081557446429, 360582081335235765, 360582081112916073, 360582080714936864, 360582080009516874, 360582078464350500, 360582076919204469, 360582075335012555, 360582074245940533, 360582073310668402]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk319B
