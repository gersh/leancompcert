import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484558343316369, 362484621483178746⟩, ⟨55178417549697308, 57967446847938548⟩, true⟩

def state01 : KState := ⟨⟨362477879290002381, 362477942449733086⟩, ⟨492006359543713365, 494796688332241217⟩, true⟩

def words00 : List Nat := [371285507907178328, 371285507909406765, 371285507718367907, 371285507525321779, 371285507331448797, 371285507188348226, 371285506970802699, 371285506980541288, 371285506989365411, 371285506991673650]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495048431095699, 362495111610936047⟩, ⟨(-631098278521632755), (-628306634260919583)⟩, true⟩

def words01 : List Nat := [371285506969468402, 371285507064065448, 371285507390991440, 371285507407320645, 371285507409075869, 371285507363115227, 371285507346311346, 371285507348766812, 371285507410437177, 371285507559725260]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482285551945621, 362482348751936032⟩, ⟨203928062301661139, 206721024880727419⟩, true⟩

def words02 : List Nat := [371285507709438014, 371285507711705435, 371285507854356913, 371285508044342770, 371285508302234438, 371285508304463096, 371285508251243340, 371285508207112510, 371285508172033981, 371285508174599654]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466358248707301, 362466421468782311⟩, ⟨1246197613427798105, 1248991890243822099⟩, true⟩

def words03 : List Nat := [371285508273651970, 371285508421912132, 371285508539808994, 371285508542037896, 371285508348694955, 371285508178226428, 371285508066781450, 371285508069010635, 371285507819800443, 371285507530674790]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486949282151791, 362487012522214674⟩, ⟨(-101396327847268283), (-98600742925665739)⟩, true⟩

def words04 : List Nat := [371285507240535181, 371285507146093722, 371285506961751980, 371285506875248789, 371285506788074592, 371285506664627309, 371285506269003904, 371285506107874462, 371285506014984180, 371285506040374433]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481461247392161, 362481524507712756⟩, ⟨257831701852347111, 260628612747728639⟩, true⟩

def words05 : List Nat := [371285506064923099, 371285506090203373, 371285506220463540, 371285506235083791, 371285506275627491, 371285506317041586, 371285506318753529, 371285506315839379, 371285506060037543, 371285506001949660]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467252661564723, 362467315941738767⟩, ⟨1188009109770077176, 1190807320376272644⟩, true⟩

def words06 : List Nat := [371285505996199496, 371285505998429809, 371285505774280051, 371285505550836728, 371285505326483453, 371285505174431257, 371285504905160170, 371285504784678116, 371285504663455956, 371285504536826232]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488711737528995, 362488775037912092⟩, ⟨(-217058866208319806), (-214259332416005506)⟩, true⟩

def words07 : List Nat := [371285504260554662, 371285504069447874, 371285503895985574, 371285503898220762, 371285503678463647, 371285503404340613, 371285503129339739, 371285503033015036, 371285502901415374, 371285502953911909]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469599169444030, 362469662489941904⟩, ⟨1034477595134768307, 1037278446144188511⟩, true⟩

def words08 : List Nat := [371285502992802996, 371285502995035718, 371285502781759070, 371285502689589322, 371285502596339627, 371285502514370162, 371285502144493389, 371285501772662407, 371285501399906927, 371285501220223538]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470061081496526, 362470124422083557⟩, ⟨1004310401764983765, 1007112568517044401⟩, true⟩

def words09 : List Nat := [371285500979891478, 371285500949422410, 371285500918199062, 371285500878562223, 371285500698121606, 371285500590100337, 371285500603120745, 371285500605352271, 371285500418747935, 371285500186488398]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654
