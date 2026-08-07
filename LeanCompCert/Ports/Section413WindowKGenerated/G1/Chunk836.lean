import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505768265310683, 362505873421048638⟩, ⟨(-1724108457855493110), (-1718172527897800664)⟩, true⟩

def state01 : KState := ⟨⟨362491059592360182, 362491164774294338⟩, ⟨(-494456863407866929), (-488518743311380971)⟩, true⟩

def words00 : List Nat := [371285321583548527, 371285321613159006, 371285321713669819, 371285321815640880, 371285321933096358, 371285321936004487, 371285321907558219, 371285321873593085, 371285321944219639, 371285322017440439]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477604659039348, 362477709867043320⟩, ⟨630610645257632130, 636550945181963098⟩, true⟩

def words01 : List Nat := [371285322162682803, 371285322309062600, 371285322445327925, 371285322448228466, 371285322409023929, 371285322378654375, 371285322455850427, 371285322458750859, 371285322379448617, 371285322291644875]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481320918690972, 362481426152691089⟩, ⟨319910900055800039, 325853373910311177⟩, true⟩

def words02 : List Nat := [371285322254559795, 371285322272313107, 371285322378334700, 371285322485555240, 371285322560774114, 371285322563674984, 371285322458518370, 371285322472490027, 371285322519099689, 371285322522102907]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486614013846951, 362486719274298933⟩, ⟨(-122793553204685984), (-116848867050703238)⟩, true⟩

def words03 : List Nat := [371285322477681776, 371285322427419340, 371285322395976806, 371285322399174845, 371285322356965642, 371285322349384077, 371285322340812114, 371285322332969732, 371285322225388054, 371285322245723824]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487910683205763, 362488015969547516⟩, ⟨(-231237825245331089), (-225290973536910877)⟩, true⟩

def words04 : List Nat := [371285322407343386, 371285322433044575, 371285322435251964, 371285322429382388, 371285322457080884, 371285322460311673, 371285322518647865, 371285322614519093, 371285322709182857, 371285322744439187]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496445419705627, 362496550732211666⟩, ⟨(-945197061353195801), (-939248020868592515)⟩, true⟩

def words05 : List Nat := [371285322880996341, 371285323019020932, 371285323298470675, 371285323404122318, 371285323477149015, 371285323551056218, 371285323619268730, 371285323626268322, 371285323762435531, 371285323899866026]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491764409942905, 362491869748647926⟩, ⟨(-553595421308024726), (-547644188886669270)⟩, true⟩

def words06 : List Nat := [371285324034161130, 371285324037063972, 371285324105460872, 371285324213716358, 371285324343628292, 371285324346550394, 371285324348412223, 371285324346498917, 371285324458030735, 371285324539568476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488423355540676, 362488528720432807⟩, ⟨(-274010843261211859), (-268057419630876647)⟩, true⟩

def words07 : List Nat := [371285324678728205, 371285324819057894, 371285324958643567, 371285324987381770, 371285325057411932, 371285325128850074, 371285325272229092, 371285325313632176, 371285325354083528, 371285325395668155]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493382673777699, 362493488064628542⟩, ⟨(-689024702308966002), (-683069106318153414)⟩, true⟩

def words08 : List Nat := [371285325497642542, 371285325529614590, 371285325681795737, 371285325835128658, 371285325951205122, 371285325954108391, 371285325925375699, 371285325974715493, 371285326165263474, 371285326265793325]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486258156033023, 362486363573385752⟩, ⟨(-92685218611682089), (-86727404550046629)⟩, true⟩

def words09 : List Nat := [371285326344437394, 371285326424063675, 371285326632458959, 371285326800671583, 371285326999631899, 371285327199733983, 371285327387466793, 371285327390370604, 371285327400069209, 371285327416057285]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836
