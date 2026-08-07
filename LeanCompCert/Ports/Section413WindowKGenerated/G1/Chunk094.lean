import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk094

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362430120846598960, 362430121952431843⟩, ⟨482000181579492333, 482007219853240657⟩, true⟩

def state01 : KState := ⟨⟨362431586283805409, 362431587392091658⟩, ⟨468309902563193338, 468316963910934020⟩, true⟩

def words00 : List Nat := [371281393861977504, 371281390266495448, 371281383156820188, 371281385245052853, 371281385245268660, 371281384698860460, 371281369128156890, 371281361335726645, 371281355400725761, 371281355401008867]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488083380060767, 362488084490837726⟩, ⟨(-63560880445354833), (-63553795647088307)⟩, true⟩

def words01 : List Nat := [371281350112933443, 371281344773402666, 371281345356087606, 371281345665024576, 371281346353152834, 371281347041239957, 371281347624047352, 371281347624322058, 371281337803066451, 371281338519534565]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362448401678449351, 362448402791672980⟩, ⟨310863783756888427, 310870891615562205⟩, true⟩

def words02 : List Nat := [371281350485091746, 371281353198322126, 371281355645877474, 371281358093007427, 371281361752786551, 371281361753088418, 371281363567509206, 371281367290244942, 371281368951687232, 371281368951971555]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362691916564529768, 362691917680240145⟩, ⟨(-1986736700687383700), (-1986729569366210690)⟩, true⟩

def words03 : List Nat := [371281373190532188, 371281380923109721, 371281399880177517, 371281406305273333, 371281409017560251, 371281411729359166, 371281425659783732, 371281436742209119, 371281459039105651, 371281481331403559]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486113239398038, 362486114357591942⟩, ⟨(-43235203512595396), (-43228048734256034)⟩, true⟩

def words04 : List Nat := [371281503641565025, 371281511027708849, 371281520941278584, 371281530852883542, 371281544158023776, 371281544158298708, 371281542553926674, 371281539818102266, 371281539960578683, 371281540444912411]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362360619082843806, 362360620203512201⟩, ⟨1143790634754535388, 1143797812929437774⟩, true⟩

def words05 : List Nat := [371281548170279929, 371281555894121303, 371281562635270548, 371281562635545955, 371281557772134656, 371281555212482984, 371281554684018702, 371281554684293968, 371281541845336382, 371281529063229901]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478613546069493, 362478614669202913⟩, ⟨27502601255847545, 27509802762618001⟩, true⟩

def words06 : List Nat := [371281516283704838, 371281514671871318, 371281514541756280, 371281520057047203, 371281523820384784, 371281523820660397, 371281512805024480, 371281512875715467, 371281519611131381, 371281519611416495]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362535561072371431, 362535562198023492⟩, ⟨(-512258271768192226), (-512251046397209412)⟩, true⟩

def words07 : List Nat := [371281519304908384, 371281514222004280, 371281515199167712, 371281515768563764, 371281519547674986, 371281523326091191, 371281527007839703, 371281527008120374, 371281527277174405, 371281532976802397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362522510974762963, 362522512102875728⟩, ⟨(-388379499796907523), (-388372251085573221)⟩, true⟩

def words08 : List Nat := [371281546729507216, 371281550707572839, 371281554058882915, 371281557409576126, 371281561276750363, 371281561277058128, 371281570052062144, 371281578946978516, 371281587734718694, 371281592046918972]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362619585198794328, 362619586329405478⟩, ⟨(-1309821117798599038), (-1309813845364817400)⟩, true⟩

def words09 : List Nat := [371281607460649855, 371281622871277737, 371281643853814396, 371281652607652426, 371281659447259071, 371281666285511260, 371281684212431013, 371281696672587054, 371281711187479580, 371281725699433390]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk094
