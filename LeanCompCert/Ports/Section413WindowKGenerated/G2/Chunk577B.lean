import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577A

def state06 : KState := ⟨⟨360550582839705078, 360550604015316569⟩, ⟨1808372747342992220, 1809199086323209270⟩, true⟩

def words05 : List Nat := [360581926577497200, 360581927105474937, 360581927433801467, 360581927559604093, 360581927608833829, 360581927658275424, 360581927658938625, 360581927606918416, 360581927255643466, 360581926714179506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576344139839543, 360576365323054118⟩, ⟨320214379179143619, 321041157351442873⟩, true⟩

def words06 : List Nat := [360581926172554578, 360581925574757579, 360581925129354367, 360581924885829394, 360581924642236105, 360581924145129957, 360581923547408964, 360581923158493686, 360581922769354917, 360581922552712271]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583519031255872, 360583540222166342⟩, ⟨(-94340895700706761), (-93513672899655007)⟩, true⟩

def words07 : List Nat := [360581922457255784, 360581922125778288, 360581921794148606, 360581921879515908, 360581921920387495, 360581921961389620, 360581921962107781, 360581921852034928, 360581921777608354, 360581921806547027]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578183598857167, 360578204797354172⟩, ⟨213933270198613978, 214760931388336236⟩, true⟩

def words08 : List Nat := [360581922134726700, 360581922238151383, 360581922238876470, 360581922059160935, 360581921879334510, 360581921439462811, 360581921157381000, 360581921166551977, 360581921167277081, 360581921027348779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618269747981653, 360618290954107632⟩, ⟨(-2102768416838216290), (-2101940314733217506)⟩, true⟩

def words09 : List Nat := [360581921198816043, 360581921434832052, 360581921969999674, 360581922588552983, 360581922953834214, 360581923319165713, 360581923842736221, 360581924574039240, 360581925203879742, 360581925833872114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577B
