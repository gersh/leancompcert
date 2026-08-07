import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk228

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462254349458546, 362462261388169412⟩, ⟨498097461568353711, 498205979974193413⟩, true⟩

def state01 : KState := ⟨⟨362466486657805292, 362466493702875075⟩, ⟨401666950818852864, 401775614241814514⟩, true⟩

def words00 : List Nat := [371284112379397448, 371284112380115012, 371284111357538547, 371284109988872124, 371284108620059895, 371284107834106816, 371284106813729603, 371284107265145977, 371284107714158684, 371284107714897952]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362550838395683894, 362550845447216926⟩, ⟨(-1522784159816169054), (-1522675348934002098)⟩, true⟩

def words01 : List Nat := [371284108092652726, 371284109242839130, 371284111171265091, 371284111912358538, 371284112475343916, 371284113038504862, 371284115521775939, 371284117046388620, 371284119970994465, 371284122895666425]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489303803915775, 362489310861892548⟩, ⟨(-118379258029422713), (-118270300067562025)⟩, true⟩

def words02 : List Nat := [371284125817840010, 371284126183551079, 371284127957139593, 371284129730954968, 371284131587890326, 371284131588605400, 371284131191239497, 371284130432893356, 371284130383632720, 371284130611353038]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470718924355637, 362470725988776717⟩, ⟨306148166294723758, 306257271413452762⟩, true⟩

def words03 : List Nat := [371284131935341988, 371284133259512517, 371284134393997276, 371284134394725094, 371284134107745562, 371284134256100013, 371284135802242519, 371284135802959483, 371284135387302507, 371284134801010231]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460033438788403, 362460040509628649⟩, ⟨550323943008518560, 550433194772800680⟩, true⟩

def words04 : List Nat := [371284134214456853, 371284134064510176, 371284133723467633, 371284134354615194, 371284134674078196, 371284134674793896, 371284132443360750, 371284130896092876, 371284129488964721, 371284129489706234]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493591967065910, 362493599044419772⟩, ⟨(-216640273322265881), (-216530872688249145)⟩, true⟩

def words05 : List Nat := [371284128436070551, 371284127376126253, 371284127169425331, 371284127333704132, 371284127610002261, 371284127886546873, 371284128085439184, 371284128086160044, 371284127001859420, 371284127417076776]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479409626048321, 362479416709790302⟩, ⟨107890888619618215, 108000435319418441⟩, true⟩

def words06 : List Nat := [371284129745083897, 371284130866891930, 371284131985746459, 371284133104753145, 371284134360655818, 371284134749648918, 371284136406656756, 371284138063801155, 371284139071765006, 371284139072506499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362556648294945986, 362556655385177611⟩, ⟨(-1658935774035173299), (-1658826078886030099)⟩, true⟩

def words07 : List Nat := [371284140571545123, 371284142277288408, 371284145602215769, 371284146382134048, 371284146792760670, 371284147203581680, 371284149524446552, 371284151075160914, 371284154244542490, 371284157413983781]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503532997501015, 362503540094198378⟩, ⟨(-443548462946972979), (-443438619828017713)⟩, true⟩

def words08 : List Nat := [371284160426324497, 371284161502456143, 371284163384647935, 371284165267028616, 371284167432046554, 371284167432763609, 371284167055178660, 371284166673575710, 371284167501849904, 371284168348978510]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362433417312809909, 362433424415958841⟩, ⟨1161925194343571730, 1162035185171554274⟩, true⟩

def words09 : List Nat := [371284170155548803, 371284171962242394, 371284173703299825, 371284173704017326, 371284172904348088, 371284172521096578, 371284172524863186, 371284172525580811, 371284170525695774, 371284168310507818]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk228
