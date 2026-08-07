import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk117

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360508344483463219, 360508345239633306⟩, ⟨891926168923883773, 891932163511808003⟩, true⟩

def state01 : KState := ⟨⟨360496615034819816, 360496615792336874⟩, ⟨1029141924832553325, 1029147935187024649⟩, true⟩

def words00 : List Nat := [360584572975214538, 360584572975357631, 360584566454698515, 360584555615855868, 360584544778838402, 360584532054299546, 360584523054537259, 360584517276872196, 360584511500179617, 360584502037869498]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525984043204092, 360525984802075811⟩, ⟨684211340622298895, 684217366846475609⟩, true⟩

def words01 : List Nat := [360584494533398171, 360584486357884977, 360584478183727118, 360584467727832936, 360584450037007370, 360584425049555250, 360584400066340987, 360584382314309769, 360584370105012001, 360584365123479094]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360503316955805287, 360503317716042367⟩, ⟨949045358563819217, 949051400796690199⟩, true⟩

def words02 : List Nat := [360584360142775811, 360584351516434202, 360584335662221123, 360584322803993255, 360584309947923305, 360584291594765390, 360584276911534194, 360584258561762633, 360584240215092883, 360584225763851122]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360281451218236718, 360281451979826945⟩, ⟨3553349099768932121, 3553355157881124493⟩, true⟩

def words03 : List Nat := [360584219180062446, 360584219493193898, 360584219493321808, 360584216169131940, 360584205627812555, 360584193223931779, 360584180822122378, 360584168297677815, 360584148560126564, 360584122776920738]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360510212375052975, 360510213137999367⟩, ⟨866686412891796278, 866692486931929442⟩, true⟩

def words04 : List Nat := [360584096998074785, 360584075771397335, 360584059173128714, 360584049769132009, 360584040366726825, 360584024634994810, 360584009264228911, 360583996225821519, 360583983189591033, 360583974200716979]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360338108898706667, 360338109663024112⟩, ⟨2889853111375786709, 2889859201532710893⟩, true⟩

def words05 : List Nat := [360583967923842075, 360583958031070968, 360583948139957509, 360583935211313617, 360583925904758862, 360583914750376651, 360583903597876317, 360583888837694019, 360583866887241793, 360583845989685057]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360247346328199637, 360247347093872130⟩, ⟨3957347725229784179, 3957353831328931077⟩, true⟩

def words06 : List Nat := [360583825095632454, 360583807209962534, 360583782136998489, 360583753422231035, 360583724712321820, 360583691919198847, 360583664049845090, 360583634184540326, 360583604324295178, 360583570868836356]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360529098381530933, 360529099148562800⟩, ⟨639394907443458215, 639401029549166293⟩, true⟩

def words07 : List Nat := [360583542305213776, 360583518328394699, 360583494355605541, 360583474965382823, 360583457692510274, 360583434087892980, 360583410487256739, 360583394033004241, 360583382281917826, 360583377673991422]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528986326090917, 360528987094497674⟩, ⟨639827468470423442, 639833606779101732⟩, true⟩

def words08 : List Nat := [360583373066830813, 360583361062614871, 360583345351033624, 360583336779668256, 360583328209719694, 360583317807847615, 360583303328383374, 360583285263464247, 360583267201580022, 360583256272341534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360333920353843556, 360333921123608815⟩, ⟨2940758949674718437, 2940765104006872387⟩, true⟩

def words09 : List Nat := [360583251669865557, 360583249049991908, 360583246430545966, 360583240230870360, 360583226877879247, 360583208342623990, 360583189810469309, 360583175681280716, 360583159627061938, 360583138505304313]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk117
