import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237A

def state06 : KState := ⟨⟨360682104386376897, 360682107713583997⟩, ⟨(-2382636176512552675), (-2382582693001950007)⟩, true⟩

def words05 : List Nat := [360581801145473143, 360581802908864572, 360581806441059022, 360581811152877171, 360581815408993518, 360581819664801834, 360581823030029741, 360581826443014570, 360581830663857310, 360581834884452145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360689281878359140, 360689285208474452⟩, ⟨(-2553259533343961268), (-2553205980719518954)⟩, true⟩

def words06 : List Nat := [360581840872173785, 360581845345286164, 360581848855182107, 360581852364817670, 360581854484921472, 360581857873963898, 360581863029476489, 360581868184614234, 360581872251456259, 360581876770431479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660711901703042, 360660715234741195⟩, ⟨(-1873937962061181302), (-1873884339946418870)⟩, true⟩

def words07 : List Nat := [360581881547279462, 360581886323819937, 360581892865829756, 360581897651839289, 360581900929995317, 360581904207899398, 360581907191836573, 360581911064943359, 360581914379082431, 360581917693008450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360706534218027970, 360706537554012589⟩, ⟨(-2964145613696204111), (-2964091921499994919)⟩, true⟩

def words08 : List Nat := [360581920118661691, 360581923169041005, 360581926774416578, 360581930379578584, 360581933158237440, 360581935982977775, 360581937909474620, 360581939835841054, 360581943525852638, 360581948763230361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617030334506735, 360617033673410222⟩, ⟨(-834320672852771860), (-834266911202132032)⟩, true⟩

def words09 : List Nat := [360581954983203488, 360581961202712705, 360581965725154345, 360581968494560659, 360581970810492635, 360581973126314739, 360581976609368078, 360581978968357330, 360581980441520064, 360581981914610083]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237B
