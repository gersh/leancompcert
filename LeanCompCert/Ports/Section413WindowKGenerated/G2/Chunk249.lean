import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565614689097680, 360565618358449457⟩, ⟨453297440277689910, 453359249811943492⟩, true⟩

def state01 : KState := ⟨⟨360568033213844679, 360568036886259084⟩, ⟨392899505597164577, 392961391406259059⟩, true⟩

def words00 : List Nat := [360583825009844074, 360583825010169233, 360583823593018788, 360583821372834294, 360583819152773795, 360583815985779506, 360583814100848339, 360583813824054064, 360583813547246105, 360583812132802893]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607612281591184, 360607615957078081⟩, ⟨(-593471970984449875), (-593410008623999491)⟩, true⟩

def words01 : List Nat := [360583811704840326, 360583811910223558, 360583812068872412, 360583812069197717, 360583810627819229, 360583807566486319, 360583804505337065, 360583803050977904, 360583803356068546, 360583804311934468]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360626589639742873, 360626593318331478⟩, ⟨(-1066764756163221419), (-1066702716493296429)⟩, true⟩

def words02 : List Nat := [360583804312228709, 360583804176043732, 360583804497745263, 360583805461738640, 360583805993041326, 360583806504138216, 360583806504433155, 360583805775916699, 360583805403136104, 360583807119763700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599685683336963, 360599689364990697⟩, ⟨(-395647633091302491), (-395585516992171375)⟩, true⟩

def words03 : List Nat := [360583810023671610, 360583812927409149, 360583815020914686, 360583817868342321, 360583820303544223, 360583822738636718, 360583825405048248, 360583827240096933, 360583827876401904, 360583828512699604]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612739232988034, 360612742917720705⟩, ⟨(-721240141922308952), (-721177949019632406)⟩, true⟩

def words04 : List Nat := [360583829072954558, 360583830434067710, 360583833397973883, 360583836361704594, 360583837968630553, 360583837979920784, 360583837980186127, 360583837624366421, 360583837989566877, 360583839148371997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249
