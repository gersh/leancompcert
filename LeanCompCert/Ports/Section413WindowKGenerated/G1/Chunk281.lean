import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk281

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362512597417085764, 362512608298295628⟩, ⟨(-773860643326557290), (-773653950467810716)⟩, true⟩

def state01 : KState := ⟨⟨362487068205440204, 362487079094721942⟩, ⟨(-56539509601610551), (-56332589881353711)⟩, true⟩

def words00 : List Nat := [371285077853843163, 371285077854738522, 371285077077790495, 371285077243495097, 371285077265459849, 371285077266361157, 371285076435549945, 371285075565385250, 371285075088369147, 371285075160678993]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473128559461628, 362473139456836168⟩, ⟨335541503293507486, 335748650543038584⟩, true⟩

def words01 : List Nat := [371285076496889753, 371285077833396887, 371285079168340360, 371285079169236224, 371285078847846259, 371285078877574950, 371285079949803282, 371285079950701650, 371285079732875882, 371285079309273688]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362518291210304306, 362518302115698187⟩, ⟨(-934539103905572894), (-934331731111652156)⟩, true⟩

def words02 : List Nat := [371285079528895677, 371285079640454413, 371285081014537297, 371285082388877731, 371285083562198605, 371285083795523436, 371285084676990734, 371285085558866659, 371285087335846447, 371285088517492946]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362512570546271016, 362512581459837375⟩, ⟨(-773585760551061710), (-773378157823705854)⟩, true⟩

def words03 : List Nat := [371285089698605706, 371285090879932304, 371285092588398921, 371285093669320796, 371285094832661892, 371285095996268563, 371285097186101747, 371285097249080964, 371285098226387023, 371285099204131334]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467278443552195, 362467289365100156⟩, ⟨501265689223672356, 501473516595632534⟩, true⟩

def words04 : List Nat := [371285101283230293, 371285101681346846, 371285101972750409, 371285102264439966, 371285102789232721, 371285102790220803, 371285103106732207, 371285103529424117, 371285103698685576, 371285103699615099]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362540087117019989, 362540098046697713⟩, ⟨(-1548621151053956049), (-1548413094790199711)⟩, true⟩

def words05 : List Nat := [371285103694825006, 371285104323289218, 371285105980652204, 371285106590962453, 371285107003678139, 371285107416634856, 371285108803294519, 371285109831885480, 371285111785202169, 371285113738797064]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488878280587543, 362488889218369434⟩, ⟨(-106417962771611852), (-106209678252189128)⟩, true⟩

def words06 : List Nat := [371285115393022679, 371285115393920157, 371285116602966801, 371285117837654643, 371285119333296378, 371285119334193999, 371285119151445934, 371285118803433111, 371285118905719808, 371285119040589015]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362433300023663586, 362433310969514577⟩, ⟨1459571540371209160, 1459780052239512776⟩, true⟩

def words07 : List Nat := [371285119553210883, 371285120066145133, 371285120577947413, 371285120578845228, 371285119413218742, 371285118168705024, 371285116923805778, 371285116592523585, 371285114795912832, 371285112958593339]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475582939897799, 362475593893802741⟩, ⟨268041768303512751, 268250507172565015⟩, true⟩

def words08 : List Nat := [371285111121014939, 371285110541353668, 371285109985586340, 371285110337056466, 371285110493505061, 371285110494405827, 371285109366652654, 371285109301846815, 371285109696603878, 371285109697533588]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479227988882273, 362479238950983423⟩, ⟨165280201579646147, 165489171540159829⟩, true⟩

def words09 : List Nat := [371285109360658507, 371285109023393154, 371285108944287004, 371285108945277289, 371285108721352122, 371285108798334961, 371285108854237770, 371285108855137845, 371285107568307204, 371285107361321727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk281
