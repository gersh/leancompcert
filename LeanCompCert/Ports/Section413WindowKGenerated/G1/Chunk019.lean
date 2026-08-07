import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk019

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362196718158010803, 362196718196445651⟩, ⟨531527775926325637, 531527825544237697⟩, true⟩

def state01 : KState := ⟨⟨362475640757622733, 362475640796480827⟩, ⟨1869109193770872, 1869159618037914⟩, true⟩

def words00 : List Nat := [371276449891111666, 371276449891163540, 371276564803354168, 371276687710252272, 371276764511083490, 371276764511130850, 371276478429034642, 371276465453163349, 371276619414032890, 371276619414081894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362816337401809325, 362816337441101787⟩, ⟨(-650032038134527016), (-650031986878402518)⟩, true⟩

def words01 : List Nat := [371276618902021093, 371276576250700672, 371276762353161493, 371276914960418065, 371277145312707171, 371277375424688107, 371277597178924268, 371277602690161275, 371277779114543310, 371277955355272322]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362235960623873280, 362235960663591405⟩, ⟨467851642990678262, 467851695066309570⟩, true⟩

def words02 : List Nat := [371278294806500274, 371278325832888787, 371278354862389202, 371278383861744909, 371278383861779392, 371278380226590020, 371278289551100815, 371278330483312919, 371278370868239473, 371278370868288975]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362849380752944415, 362849380793097306⟩, ⟨(-717671107139385917), (-717671054222452541)⟩, true⟩

def words03 : List Nat := [371278385197410429, 371278524917941407, 371278929493545144, 371278981661207744, 371278992866501812, 371279004060241655, 371279172150703376, 371279256474174575, 371279447259939361, 371279637849139320]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513800865763507, 362513800906352958⟩, ⟨(-67177381655366373), (-67177327889245681)⟩, true⟩

def words04 : List Nat := [371279829535479340, 371279829535527716, 371279684020716487, 371279695639946056, 371279785738501337, 371279785738550588, 371279663708214609, 371279472733481925, 371279350994559484, 371279368652181126]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362159784821445112, 362159784862473345⟩, ⟨626722343105136636, 626722397729146260⟩, true⟩

def words05 : List Nat := [371279645651983938, 371279922368140968, 371280161808369792, 371280161808418403, 371280056475847644, 371279936557441480, 371279869684463454, 371279869684512527, 371279704412049465, 371279541187845359]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361956978995120712, 361956979036586263⟩, ⟨1027360711072661711, 1027360766556073681⟩, true⟩

def words06 : List Nat := [371279390182902015, 371279390182956152, 371279331545139693, 371279380730230128, 371279384657135857, 371279384657184821, 371279048627429294, 371278817890098904, 371278587387113312, 371278481963772088]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471466067894335, 362471466109808316⟩, ⟨11585199105380334, 11585255474445408⟩, true⟩

def words07 : List Nat := [371278217375819788, 371277957586821290, 371277698061147540, 371277691585589357, 371277607084973164, 371277595191827588, 371277583310696390, 371277574791783118, 371277320205489758, 371277317248936824]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362069177107099117, 362069177149454330⟩, ⟨809944526379622059, 809944583624648509⟩, true⟩

def words08 : List Nat := [371277417154957259, 371277417155006705, 371277185662441006, 371276958484170915, 371276731534776459, 371276577704892573, 371276296577529654, 371276264672803819, 371276232800142814, 371276184477908928]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362813215634822533, 362813215677627722⟩, ⟨(-675336909769308252), (-675336851626535218)⟩, true⟩

def words09 : List Nat := [371275980054372690, 371275900500209304, 371275989237143538, 371275989237193290, 371275827122984804, 371275620958657809, 371275455817784039, 371275455817839436, 371275547251757993, 371275716001652443]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk019
