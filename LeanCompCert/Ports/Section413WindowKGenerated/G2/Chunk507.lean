import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592151776232555, 360592167920208652⟩, ⟨(-514623357045982415), (-514070297607514627)⟩, true⟩

def state01 : KState := ⟨⟨360596226078925490, 360596242229502869⟩, ⟨(-721348418922321469), (-720795024765286085)⟩, true⟩

def words00 : List Nat := [360582028857590798, 360582028858291426, 360582028781450874, 360582028510069666, 360582028238584947, 360582027869946988, 360582027921789179, 360582028142178865, 360582028167941335, 360582028448966787]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590013668577635, 360590029825763579⟩, ⟨(-406432389864697848), (-405878660555597024)⟩, true⟩

def words01 : List Nat := [360582028666876164, 360582028884979633, 360582029090759057, 360582029091459825, 360582028909497938, 360582028343902935, 360582027778195830, 360582027441946064, 360582027485516221, 360582027644013306]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586203323365960, 360586219487237286⟩, ⟨(-213228597043546624), (-212674528619708666)⟩, true⟩

def words02 : List Nat := [360582027644642586, 360582027475338078, 360582027544739608, 360582027773848168, 360582027900389909, 360582027916677310, 360582027917302122, 360582027682678735, 360582027447938368, 360582027286637659]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556972219548545, 360556988390020041⟩, ⟨1269873503313233665, 1270427906596894741⟩, true⟩

def words03 : List Nat := [360582027647797950, 360582028009082918, 360582028175480021, 360582028176181114, 360582027955025200, 360582027574556471, 360582027193883962, 360582027125589616, 360582026878554533, 360582026385814225]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574510655557956, 360574526832656398⟩, ⟨379855819887985586, 380410559455545290⟩, true⟩

def words04 : List Nat := [360582025892934165, 360582025875465673, 360582025876046347, 360582025763329025, 360582025650563274, 360582025176226661, 360582024314454489, 360582023689461602, 360582023064289023, 360582022607226951]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583520030316657, 360583536214097325⟩, ⟨(-77399516074644217), (-76844437350906231)⟩, true⟩

def words05 : List Nat := [360582022460160551, 360582022117032562, 360582021817346911, 360582022156240855, 360582022397758186, 360582022639380415, 360582022640016144, 360582022583853222, 360582022335484708, 360582022366116574]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583692311506337, 360583708501892857⟩, ⟨(-86182967936201743), (-85627553865902523)⟩, true⟩

def words06 : List Nat := [360582022575519645, 360582022658125661, 360582022658750690, 360582022547243568, 360582022435620641, 360582021983937503, 360582021857656572, 360582021988495166, 360582021989126118, 360582021957332658]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605541035084870, 360605557232106825⟩, ⟨(-1195602642990528728), (-1195046892006850946)⟩, true⟩

def words07 : List Nat := [360582021981696963, 360582022006256183, 360582022417638470, 360582022568790409, 360582022569438228, 360582022396188475, 360582022435847954, 360582022956957400, 360582023420982501, 360582023885146213]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581883254877819, 360581899458575810⟩, ⟨5667120966962158, 6223210993457840⟩, true⟩

def words08 : List Nat := [360582024155192141, 360582024155893992, 360582024166484220, 360582024294552097, 360582024295149711, 360582024153042487, 360582023750371306, 360582023033575940, 360582022316674481, 360582021986848964]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551689471497219, 360551705681816080⟩, ⟨1539400292345477108, 1539956718678691930⟩, true⟩

def words09 : List Nat := [360582022097016586, 360582022209735989, 360582022210361363, 360582022129205384, 360582021754641463, 360582021283407315, 360582020811976778, 360582020627599166, 360582020386470054, 360582019790451488]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507
