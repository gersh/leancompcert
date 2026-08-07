import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486255871766419, 362486383297426243⟩, ⟨(-125345534096705984), (-117456146954342774)⟩, true⟩

def state01 : KState := ⟨⟨362478478346691723, 362478605801251522⟩, ⟨587871493017417895, 595763530438368151⟩, true⟩

def words00 : List Nat := [371285102445373435, 371285102448593366, 371285102352571407, 371285102366758079, 371285102415799767, 371285102419004405, 371285102309810699, 371285102158664007, 371285102006244839, 371285101968849804]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479234826977952, 362479362310418953⟩, ⟨518535422098888058, 526430108364950794⟩, true⟩

def words01 : List Nat := [371285101948170926, 371285101999674741, 371285102047409316, 371285102050670188, 371285101999341807, 371285101957676115, 371285101958605034, 371285101961832118, 371285101903909799, 371285101844962837]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474782536102749, 362474910048294479⟩, ⟨926951063985022339, 934848387405620751⟩, true⟩

def words02 : List Nat := [371285101784598360, 371285101775093403, 371285101711059208, 371285101720637027, 371285101723120341, 371285101713652195, 371285101544789559, 371285101465765871, 371285101384929674, 371285101353073784]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476724498668031, 362476852039987649⟩, ⟨748820020982974611, 756720016454762745⟩, true⟩

def words03 : List Nat := [371285101244369842, 371285101136564364, 371285101034953891, 371285101038486718, 371285100988978111, 371285100945451701, 371285100900837524, 371285100857380356, 371285100654567245, 371285100568616980]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468674185640046, 362468801755546223⟩, ⟨1487431610187766264, 1495334228337712446⟩, true⟩

def words04 : List Nat := [371285100480890264, 371285100473528408, 371285100366426158, 371285100256047282, 371285100144395787, 371285100054371991, 371285099904355971, 371285099840890313, 371285099776420764, 371285099676291049]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486669111286752, 362486796710202400⟩, ⟨(-163714714291283278), (-155809434378065182)⟩, true⟩

def words05 : List Nat := [371285099500852756, 371285099367932611, 371285099233323596, 371285099218469597, 371285099088900083, 371285098940773145, 371285098791309591, 371285098761908878, 371285098696150678, 371285098718306300]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483302821287329, 362483430449177018⟩, ⟨145156154570675186, 153064093287927888⟩, true⟩

def words06 : List Nat := [371285098739698827, 371285098742928875, 371285098675885299, 371285098659962435, 371285098659119067, 371285098662334703, 371285098560021898, 371285098458877405, 371285098356401012, 371285098359096251]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471725605146934, 362471853261861661⟩, ⟨1207707409087013023, 1215617993225116797⟩, true⟩

def words07 : List Nat := [371285098443577340, 371285098547507696, 371285098623564171, 371285098626771721, 371285098544442791, 371285098499490830, 371285098452866654, 371285098455999944, 371285098314255605, 371285098173533323]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479344924648885, 362479472610057933⟩, ⟨508398890638515117, 516312108487838051⟩, true⟩

def words08 : List Nat := [371285098031398474, 371285098009289962, 371285097926311324, 371285097919491284, 371285097911560622, 371285097881931512, 371285097693114897, 371285097612972387, 371285097534380526, 371285097537702425]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476797391842754, 362476925106590503⟩, ⟨742236149180028930, 750152060166506786⟩, true⟩

def words09 : List Nat := [371285097478888174, 371285097403703611, 371285097327186121, 371285097300165319, 371285097212668004, 371285097132428337, 371285097051136264, 371285096959146326, 371285096782613960, 371285096697659855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk917
