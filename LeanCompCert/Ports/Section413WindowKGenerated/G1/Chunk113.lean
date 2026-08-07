import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk113

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362559419219119269, 362559420844554139⟩, ⟨(-825766743716548154), (-825754311296898002)⟩, true⟩

def state01 : KState := ⟨⟨362445154566060585, 362445156194502595⟩, ⟨465683214832165575, 465695681247902367⟩, true⟩

def words00 : List Nat := [371286358176402617, 371286358176735909, 371286356697361457, 371286359153930240, 371286360744912022, 371286360745245465, 371286351941694365, 371286343149959748, 371286334359646153, 371286331763136362]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362377499382793148, 362377501014247389⟩, ⟨1231729951777995497, 1231742452277460549⟩, true⟩

def words01 : List Nat := [371286332274568566, 371286336425724034, 371286340457627863, 371286340457961724, 371286334110232817, 371286329732440092, 371286328763097166, 371286328763431206, 371286321797709106, 371286312184943278]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362517842101877949, 362517843736325683⟩, ⟨(-357564418612180119), (-357551884211321587)⟩, true⟩

def words02 : List Nat := [371286302573725408, 371286300743795933, 371286295829262912, 371286295300784441, 371286294772298509, 371286292796710615, 371286284365414546, 371286282239846013, 371286285758553840, 371286288544002736]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362439278755098549, 362439280392594833⟩, ⟨533251039633862961, 533263608589978587⟩, true⟩

def words03 : List Nat := [371286291285568446, 371286294026757190, 371286300037206269, 371286302157624230, 371286306588070757, 371286311017867552, 371286315451315390, 371286315451649917, 371286309548942071, 371286305402170669]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362350437058675770, 362350438699151732⟩, ⟨1541305640732497446, 1541318243493739842⟩, true⟩

def words04 : List Nat := [371286301255939241, 371286301064163863, 371286292112732004, 371286283198689945, 371286274286087863, 371286267688614236, 371286257890113300, 371286251366941864, 371286244844814292, 371286237663336203]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362526562865780398, 362526564509288387⟩, ⟨(-458412623623295648), (-458399986433436262)⟩, true⟩

def words05 : List Nat := [371286225699951722, 371286221473966662, 371286220757402574, 371286220757743278, 371286217829550494, 371286213670329390, 371286211085461996, 371286211085834125, 371286212397425906, 371286215949616401]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473635748725199, 362473637395261807⟩, ⟨142837286000753351, 142849957611459987⟩, true⟩

def words06 : List Nat := [371286217842243510, 371286217842581467, 371286216230935674, 371286217401759167, 371286220884729572, 371286220885065013, 371286214084259141, 371286207203882907, 371286201155443796, 371286201155825700]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362420669878288273, 362420671527844336⟩, ⟨745731545692490885, 745744251649705527⟩, true⟩

def words07 : List Nat := [371286205509229492, 371286210966700859, 371286215055973813, 371286215056311837, 371286213190262084, 371286211441050968, 371286214184599410, 371286214184935156, 371286208415743099, 371286202657163291]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362460705287477523, 362460706940044824⟩, ⟨290276838820063627, 290289579060564789⟩, true⟩

def words08 : List Nat := [371286196899451041, 371286196597544125, 371286198318200529, 371286203020997519, 371286204912467256, 371286204912803270, 371286196557662267, 371286194383944631, 371286193294310674, 371286193294659448]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504604966180932, 362504606621817323⟩, ⟨(-209866081369162939), (-209853306156596895)⟩, true⟩

def words09 : List Nat := [371286191057499792, 371286188837526048, 371286192066544668, 371286193783505153, 371286197030072488, 371286200276203709, 371286202871864015, 371286202872200721, 371286198436646836, 371286200051678161]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk113
