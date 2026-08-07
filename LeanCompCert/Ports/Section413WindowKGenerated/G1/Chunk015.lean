import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk015

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362999574416107072, 362999574439435922⟩, ⟨(-828416754885515861), (-828416731075358939)⟩, true⟩

def state01 : KState := ⟨⟨362130019726665341, 362130019750321275⟩, ⟨481116083341430135, 481116107643930055⟩, true⟩

def words00 : List Nat := [371248329480966073, 371248410869497741, 371248477458110966, 371248543958246602, 371248614370092938, 371248614370133231, 371248525775175418, 371248582636811494, 371248639689120254, 371248639689158315]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362571251595939020, 362571251619930585⟩, ⟨(-185999939726292220), (-185999914915321996)⟩, true⟩

def words01 : List Nat := [371248651029789324, 371248872943644165, 371249335588381832, 371249335588418775, 371249224501975479, 371249024970675124, 371248877983603372, 371248877983644399, 371248883254812729, 371248963707428730]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362177839671049495, 362177839695377662⟩, ⟨412580743448068903, 412580768772428311⟩, true⟩

def words02 : List Nat := [371249040337818529, 371249040337855747, 371248549875645515, 371248484907219646, 371248459283959237, 371248459283997154, 371248166271790924, 371247875220598117, 371247584550098371, 371247500328562256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361864931841579018, 361864931866245502⟩, ⟨896473713193271403, 896473739036968241⟩, true⟩

def words03 : List Nat := [371247568671354204, 371247812828868776, 371247982707425222, 371247982707462895, 371247779107758631, 371247696324168542, 371247802396486713, 371247802396524313, 371247435920158069, 371247057670814962]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361959804141816043, 361959804166820871⟩, ⟨751740378595735409, 751740404962238651⟩, true⟩

def words04 : List Nat := [371246679912369308, 371246558683830399, 371246316095841230, 371246401666424941, 371246413068106251, 371246413068144124, 371245874956509826, 371245378236753641, 371244882158320981, 371244797976473929]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362456163476229038, 362456163501581553⟩, ⟨(-20377251241633678), (-20377224334457006)⟩, true⟩

def words05 : List Nat := [371244485279010959, 371244083365338564, 371243691124853629, 371243691124896142, 371243553049158270, 371243534170343926, 371243515315767959, 371243492009447762, 371243101178242841, 371243109546210345]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362317989224456688, 362317989250152294⟩, ⟨196136869566884402, 196136897011053702⟩, true⟩

def words06 : List Nat := [371243262240645382, 371243262240683940, 371243078229806973, 371242891116776892, 371242704242854809, 371242637450585687, 371242577177577822, 371242748216529640, 371242917209992183, 371242917210031947]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362895246373084534, 362895246399128597⟩, ⟨(-713410813055319418), (-713410785062256494)⟩, true⟩

def words07 : List Nat := [371243159129008906, 371243480160606202, 371243923484245052, 371243923484283680, 371243835269340144, 371243647459205488, 371243545569253064, 371243545569295544, 371243720585755147, 371244006180872901]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362639254211631522, 362639254238027533⟩, ⟨(-307610230320418384), (-307610201769469238)⟩, true⟩

def words08 : List Nat := [371244253789427953, 371244253789467448, 371244529813429539, 371244865387660771, 371245316792414714, 371245422316443355, 371245498027269471, 371245573642814412, 371245788702279151, 371245910302283053]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362160033630550482, 362160033657300841⟩, ⟨458064272065517291, 458064301181690421⟩, true⟩

def words09 : List Nat := [371246284537586985, 371246658303057025, 371247002851252242, 371247002851291468, 371246829517437046, 371246640527567188, 371246651566285754, 371246651566325289, 371246502888764475, 371246323845539398]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk015
