import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249A

def state06 : KState := ⟨⟨360557032308845455, 360557035996678937⟩, ⟨669094359232835700, 669156629516700436⟩, true⟩

def words05 : List Nat := [360583839498661498, 360583839848958436, 360583841800976574, 360583844552397110, 360583845900596071, 360583847248735683, 360583847536396909, 360583847536722810, 360583846230270361, 360583845156515344]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608998901231893, 360609002592138749⟩, ⟨(-628274228476247330), (-628211881465596190)⟩, true⟩

def words06 : List Nat := [360583844201134003, 360583844364447705, 360583844364738272, 360583843555918583, 360583842747110656, 360583841528293844, 360583842672840302, 360583844045106570, 360583844045402494, 360583844933996681]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360668552128379462, 360668555822362846⟩, ⟨(-2115829889130248509), (-2115767465283420865)⟩, true⟩

def words07 : List Nat := [360583847541031143, 360583850147951999, 360583852410769766, 360583853081217981, 360583853081522250, 360583852248474638, 360583852180987575, 360583853973597481, 360583857364648062, 360583860755500694]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360626253830958605, 360626257528055100⟩, ⟨(-1059598921220609225), (-1059536419593317863)⟩, true⟩

def words08 : List Nat := [360583862927135497, 360583863506961043, 360583863596754883, 360583863686635408, 360583863686909275, 360583862976752335, 360583862215585126, 360583860648326033, 360583859111525676, 360583860808452311]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536683811519857, 360536687511688331⟩, ⟨1179395031823839449, 1179457610235706293⟩, true⟩

def words09 : List Nat := [360583863579179762, 360583866349749906, 360583868322121201, 360583868703970219, 360583868704243605, 360583868676410397, 360583868648488748, 360583868573938958, 360583867702967169, 360583865816097760]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249B
