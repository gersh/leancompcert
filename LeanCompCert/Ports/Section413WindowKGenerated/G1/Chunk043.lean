import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk043

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362561773389463640, 362561773604051782⟩, ⟨(-341125626445401833), (-341125000861622319)⟩, true⟩

def state01 : KState := ⟨⟨362442995064255233, 362442995279885725⟩, ⟨170204510068060349, 170205140139388025⟩, true⟩

def words00 : List Nat := [371282484722621261, 371282484722750450, 371282512718668044, 371282543498895149, 371282556603347149, 371282556603463632, 371282498082616583, 371282479844958574, 371282486031537655, 371282486031658205]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362422031111044505, 362422031327743234⟩, ⟨261170972411950449, 261171607092654615⟩, true⟩

def words01 : List Nat := [371282476871284579, 371282468257286462, 371282486709731851, 371282487575210132, 371282504399566478, 371282521216171976, 371282537307408402, 371282537307525559, 371282501715901940, 371282487718273942]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362270266370134038, 362270266587875868⟩, ⟨917597601219004658, 917598240411386416⟩, true⟩

def words02 : List Nat := [371282495429277185, 371282495429394143, 371282446135613343, 371282386711488558, 371282327314799963, 371282282870240194, 371282219320942267, 371282208999298603, 371282198682384991, 371282183040626766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362624156778219789, 362624156997023147⟩, ⟨(-616866912890440429), (-616866269096262651)⟩, true⟩

def words03 : List Nat := [371282134110563027, 371282125380894675, 371282129636564109, 371282129636682218, 371282096690831388, 371282049899531803, 371282009342537691, 371282009342668050, 371282021911845329, 371282054654453172]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480437348849471, 362480437568713646⟩, ⟨6923943685583540, 6924592089193312⟩, true⟩

def words04 : List Nat := [371282086799610459, 371282086799728554, 371282092740877219, 371282114736848183, 371282138739424665, 371282138739542446, 371282106855147851, 371282063451471375, 371282029428829841, 371282029428964036]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362402712439001864, 362402712659929269⟩, ⟨346306098183686133, 346306751217749501⟩, true⟩

def words05 : List Nat := [371282064186043535, 371282099292895419, 371282133857256746, 371282133857376555, 371282125496339056, 371282125075703870, 371282176782091271, 371282176782209234, 371282159035390982, 371282140813878295]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454108778679826, 362454109000667064⟩, ⟨122348652510202697, 122349310170484801⟩, true⟩

def words06 : List Nat := [371282122923211464, 371282122923341318, 371282124398780108, 371282151332513721, 371282165875513930, 371282165875632138, 371282124336822490, 371282108028393020, 371282106554359140, 371282106554481821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362531970160551827, 362531970383615667⟩, ⟨(-217988290653679831), (-217987628283056075)⟩, true⟩

def words07 : List Nat := [371282100149273650, 371282093081785823, 371282131121588118, 371282150076783522, 371282171605193532, 371282193123810675, 371282214148941505, 371282214149060728, 371282201518566090, 371282212878871761]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362410036108875838, 362410036332999867⟩, ⟨317489717779545741, 317490384799343357⟩, true⟩

def words08 : List Nat := [371282256589528887, 371282258002057466, 371282259645187894, 371282261287609141, 371282278151400114, 371282278151531187, 371282308437431084, 371282341671007864, 371282357605040644, 371282357605163727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362838720084292162, 362838720309495224⟩, ⟨(-1566416681738368091), (-1566416009976181779)⟩, true⟩

def words09 : List Nat := [371282376346164004, 371282411541538656, 371282482129958215, 371282502921205557, 371282516716106768, 371282530504770920, 371282595836063396, 371282635742336175, 371282716670728275, 371282797562397705]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk043
