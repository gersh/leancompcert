import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk011

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨363508212628365358, 363508212640428980⟩, ⟨(-1181583829476459723), (-1181583820445008239)⟩, true⟩

def state01 : KState := ⟨⟨363589380127380691, 363589380139677452⟩, ⟨(-1273445701559196618), (-1273445692270090300)⟩, true⟩

def words00 : List Nat := [371235978106374289, 371236241817118264, 371237323766824340, 371238403758263759, 371239531071602243, 371240031804608378, 371240461474995004, 371240890370510899, 371242131768233457, 371243164395059909]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362942765944248517, 362942765956781780⟩, ⟨(-551987890513252291), (-551987880960410047)⟩, true⟩

def words01 : List Nat := [371244523209880513, 371245879582995875, 371247083310879426, 371247224473395134, 371247557290339923, 371247889511385140, 371249021139592932, 371249479199841377, 371249919634465505, 371250359283311299]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨363384895626103109, 363384895638873484⟩, ⟨(-1046588956695210384), (-1046588946875571436)⟩, true⟩

def words02 : List Nat := [371251261379125130, 371251927630408429, 371253383460186775, 371254836701833592, 371256162057187062, 371256447590360177, 371256941894180350, 371257435322364819, 371258710730106542, 371259529638099328]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362890171283473498, 362890171296487276⟩, ⟨(-483153059391396715), (-483153049295461617)⟩, true⟩

def words03 : List Nat := [371260303472409906, 371261075940737309, 371262182615353281, 371263004095916939, 371264010993195087, 371265016119336195, 371266006799553466, 371266006799580274, 371266352832160328, 371266724276946995]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361930615665594149, 361930615678849024⟩, ⟨614881749064322239, 614881759436360119⟩, true⟩

def words04 : List Nat := [371267364673797365, 371267364673824345, 371266997643985376, 371266613124646230, 371266229276945994, 371266040653455670, 371265486065070456, 371265425485333548, 371265365011035177, 371265295469663251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362812505080359159, 362812505093860818⟩, ⟨(-401577997569357668), (-401577986912270928)⟩, true⟩

def words05 : List Nat := [371265113297741527, 371265395171050657, 371266421366083718, 371266460733573456, 371266460733595031, 371266223132159504, 371266183863652244, 371266183863682262, 371266317174077959, 371266615354918294]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362656147059422558, 362656147073173506⟩, ⟨(-219529048833979562), (-219529037886437646)⟩, true⟩

def words06 : List Nat := [371266889478756776, 371266889478784694, 371267029590416458, 371267464579080400, 371268099930692211, 371268141328302422, 371268176786284863, 371268212183613081, 371268515416828537, 371268675648846916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362070132080918544, 362070132094919614⟩, ⟨472518789090907154, 472518800332384996⟩, true⟩

def words07 : List Nat := [371269555459558280, 371270433770176946, 371271181474768127, 371271181474795940, 371270977866283163, 371270955577932752, 371271241875591683, 371271241875619635, 371270911399665900, 371270571756218246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497991590932167, 362497991605184889⟩, ⟨(-32919245993947110), (-32919234454235254)⟩, true⟩

def words08 : List Nat := [371270602790957659, 371270625072168713, 371270825752911452, 371271026094963666, 371271132181200338, 371271132181228436, 371270306589338460, 371270185580589697, 371270328382924758, 371270351609841283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362265815681842460, 362265815696353744⟩, ⟨247750370343000146, 247750382191728690⟩, true⟩

def words09 : List Nat := [371270360930452533, 371270370235447884, 371271074310638733, 371271437153589626, 371271989160969665, 371272540246042187, 371272950009951303, 371272950009979784, 371272446540515047, 371272274348180185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk011
