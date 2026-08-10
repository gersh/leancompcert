import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497A

def state06 : KState := ⟨⟨360623699934980661, 360623715462102078⟩, ⟨(-2081663797871962882), (-2081141723977888266)⟩, true⟩

def words05 : List Nat := [360581887618273645, 360581888384074445, 360581889211986577, 360581889636997595, 360581889733669550, 360581889830402574, 360581890329733025, 360581891032611296, 360581891873690972, 360581892714890851]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592934167497941, 360592949701174707⟩, ⟨(-550825181193706778), (-550302781075187986)⟩, true⟩

def words06 : List Nat := [360581893279862757, 360581893543739992, 360581893798860833, 360581894054172300, 360581894106113709, 360581894106800369, 360581893871307866, 360581893403035487, 360581892934650529, 360581893005888794]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360532029330497559, 360532044870638825⟩, ⟨2480852872895425679, 2481375594784230249⟩, true⟩

def words07 : List Nat := [360581893515452659, 360581894025128417, 360581894296185495, 360581894340809329, 360581894341388671, 360581894122249621, 360581893902928337, 360581893507386611, 360581892709272006, 360581891708621634]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614358479655849, 360614374026278736⟩, ⟨(-1617957879687597634), (-1617434835111415368)⟩, true⟩

def words08 : List Nat := [360581890707854544, 360581889991896339, 360581889478844229, 360581889368269072, 360581889257632763, 360581888799544706, 360581888442766596, 360581888466008177, 360581888891298228, 360581889544442432]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590569259525665, 360590584812698097⟩, ⟨(-433436883967430847), (-432913513257347267)⟩, true⟩

def words09 : List Nat := [360581889884945241, 360581890225498876, 360581890499584053, 360581891015167877, 360581891310210767, 360581891605353202, 360581891605975113, 360581891594566389, 360581891769478810, 360581891944818791]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497B
