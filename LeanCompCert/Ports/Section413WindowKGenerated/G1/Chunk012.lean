import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk012

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362265815681842460, 362265815696353744⟩, ⟨247750370343000146, 247750382191728690⟩, true⟩

def state01 : KState := ⟨⟨361986958323412807, 361986958338179102⟩, ⟨584803760365459109, 584803772521542583⟩, true⟩

def words00 : List Nat := [371272615344404156, 371272615344432709, 371272220831162378, 371271817602096299, 371271415042279185, 371271207371623339, 371270686931953699, 371270543062070943, 371270399430176809, 371270267241089468]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362980171171120884, 362980171186147671⟩, ⟨(-623042416109085113), (-623042403636460841)⟩, true⟩

def words01 : List Nat := [371269868142097959, 371269732378540035, 371270129906867041, 371270129906895872, 371269774627253084, 371269312496018486, 371269054881234527, 371269061749150220, 371269480691331524, 371269898947297171]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468793153525499, 362468793168815358⟩, ⟨939757832991355, 939770627915849⟩, true⟩

def words02 : List Nat := [371270142042843264, 371270142042872544, 371270174866734969, 371270520403349900, 371270898289637140, 371270898289666352, 371270404104928806, 371269903656577945, 371269557209943029, 371269557209976266]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361855245761413467, 361855245776969218⟩, ⟨763146712509614163, 763146725632960559⟩, true⟩

def words03 : List Nat := [371270206498044854, 371270855352602258, 371271489090388797, 371271489090418241, 371271260709333936, 371271132841561575, 371271523093259072, 371271523093288646, 371271183408600912, 371270686684737735]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362403841108903570, 362403841124725706⟩, ⟨80781951745324213, 80781965200350401⟩, true⟩

def words04 : List Nat := [371270190761383542, 371270065493389348, 371269665699614595, 371269583577128656, 371269501586557621, 371269330586138337, 371268660405663700, 371268384593235166, 371268466696855126, 371268466696885987]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362774331262968046, 362774331279063554⟩, ⟨(-384725476938345467), (-384725463140213093)⟩, true⟩

def words05 : List Nat := [371268415037778160, 371268367187464692, 371268515944658748, 371268538057087997, 371268738982823871, 371268939588880326, 371269130292535526, 371269130292565724, 371268993609867191, 371269235749214060]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361518855083950844, 361518855100316041⟩, ⟨1204287009261375755, 1204287023400753899⟩, true⟩

def words06 : List Nat := [371269820439095537, 371269820439125735, 371269581609017142, 371269336609624380, 371269091997571041, 371268792965677922, 371268192390628359, 371267839780906624, 371267487726903913, 371267112599056793]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨363016377911718038, 363016377928359487⟩, ⟨(-706027261318908594), (-706027246827295980)⟩, true⟩

def words07 : List Nat := [371266366527088135, 371266017470735981, 371265709969253097, 371265709969284211, 371265384370153776, 371264899140526922, 371264532484805481, 371264532484839277, 371264794141741171, 371265224730211715]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362229296789131986, 362229296806050626⟩, ⟨302273320127274443, 302273334975132687⟩, true⟩

def words08 : List Nat := [371265514694099614, 371265514694130238, 371265098167530416, 371265189054488009, 371265451219086993, 371265451219117734, 371264920747372396, 371264287997271957, 371263656228927545, 371263617220760032]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362068597662450824, 362068597679648890⟩, ⟨512797036731409079, 512797051941150449⟩, true⟩

def words09 : List Nat := [371263844995504603, 371264253640226717, 371264657636467548, 371264657636498553, 371264277763061558, 371263876906055147, 371263662368095357, 371263662368126671, 371263360614133928, 371263056950372852]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk012
