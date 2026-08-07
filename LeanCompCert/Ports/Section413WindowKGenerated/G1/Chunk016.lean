import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk016

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362160033630550482, 362160033657300841⟩, ⟨458064272065517291, 458064301181690421⟩, true⟩

def state01 : KState := ⟨⟨363121288678295396, 363121288705400435⟩, ⟨(-1084808902927848577), (-1084808873242345439)⟩, true⟩

def words00 : List Nat := [371246353920881736, 371246377299152923, 371246540300826454, 371246703099397570, 371246803105624625, 371246803105664512, 371246763913731536, 371246936862251313, 371247494374152231, 371247912620209656]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨363063271014269031, 363063271041737539⟩, ⟨(-989788711265835437), (-989788680993272827)⟩, true⟩

def words01 : List Nat := [371248327391692335, 371248741648902038, 371249538520294221, 371250150790646537, 371250783428757587, 371251415284400236, 371251916656346243, 371251916656386280, 371252290374408674, 371252667290353657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362924085897074906, 362924085924900990⟩, ⟨(-762719262994073377), (-762719232140362443)⟩, true⟩

def words02 : List Nat := [371253424311896584, 371253677842889868, 371253923112591643, 371254168080437343, 371254485219311790, 371254620761126822, 371255133944494405, 371255646497818542, 371256160015570822, 371256446910713153]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨363599460719946430, 363599460748138870⟩, ⟨(-1867642628917681467), (-1867642597464976545)⟩, true⟩

def words03 : List Nat := [371256872254930163, 371257297078231687, 371257951338691917, 371258263223436047, 371258526165346907, 371258788786021335, 371259424739272731, 371259959468343025, 371260654286224409, 371261348257300981]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362619123795310744, 362619123823869680⟩, ⟨(-256512415583907522), (-256512383528232838)⟩, true⟩

def words04 : List Nat := [371262031215075435, 371262223425731102, 371262681349072675, 371263138715688585, 371263609053568427, 371263609053609158, 371263591351710478, 371263553037241265, 371263661773199987, 371263755935603034]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362006776635084450, 362006776664011456⟩, ⟨759057930262996237, 759057962927900273⟩, true⟩

def words05 : List Nat := [371264067542484437, 371264378772362504, 371264663212098815, 371264663212139710, 371264464883961332, 371264366397321422, 371264532310801805, 371264532310842763, 371264316123235387, 371264040497100553]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362895115320283813, 362895115349579004⟩, ⟨(-720009015352980934), (-720008982074991816)⟩, true⟩

def words06 : List Nat := [371263765202828307, 371263653136617198, 371263445436576561, 371263521749639030, 371263521749671228, 371263513072628083, 371263384060307661, 371263498999776031, 371263972246497466, 371264230261562851]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362571448007842314, 362571448037515131⟩, ⟨(-176905687386973576), (-176905653476455692)⟩, true⟩

def words07 : List Nat := [371264477716543257, 371264724875716182, 371265104619163118, 371265326569836271, 371265635954230324, 371265944969665889, 371266249480904304, 371266249480945736, 371266147053250791, 371266209695173397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362020328729814072, 362020328759856447⟩, ⟨752495990296627719, 752496024829962229⟩, true⟩

def words08 : List Nat := [371266544461315083, 371266544461356583, 371266492332417869, 371266335654450204, 371266179162435311, 371266117568811697, 371265887677947756, 371265792110119553, 371265696655442307, 371265592679874177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨363480907162042295, 363480907192461209⟩, ⟨(-1723485868369978695), (-1723485833198365395)⟩, true⟩

def words09 : List Nat := [371265329365934629, 371265293298286992, 371265568040521094, 371265681059594175, 371265753482372833, 371265825819810889, 371266243852658763, 371266495283499543, 371267091996415737, 371267688007747297]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk016
