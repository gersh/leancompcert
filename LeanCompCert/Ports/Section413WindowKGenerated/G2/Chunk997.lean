import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570134362252493, 360570200220888005⟩, ⟨1215207549536387012, 1219641135696652678⟩, true⟩

def state01 : KState := ⟨⟨360590697108999926, 360590762981346699⟩, ⟨(-835051531526851562), (-830616578288819142)⟩, true⟩

def words00 : List Nat := [360582433210071602, 360582433086473911, 360582433046568545, 360582433068561568, 360582433069904411, 360582432987353219, 360582432804188149, 360582432722012551, 360582432656116211, 360582432741169700]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587247857090274, 360587313743245708⟩, ⟨(-491111887236226035), (-486675557068948997)⟩, true⟩

def words01 : List Nat := [360582432774903760, 360582432808785856, 360582432942909185, 360582433127708859, 360582433211803848, 360582433296103394, 360582433320837058, 360582433322287491, 360582433320826918, 360582433371437675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601415852696456, 360601481752530283⟩, ⟨(-1903976796524174304), (-1899539102278620438)⟩, true⟩

def words02 : List Nat := [360582433522062702, 360582433718746534, 360582433851829170, 360582433985061545, 360582434092437305, 360582434276833841, 360582434521387123, 360582434766214908, 360582434933598931, 360582435126082352]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606582730679299, 360606648644204294⟩, ⟨(-2419313784922399415), (-2414874725188267263)⟩, true⟩

def words03 : List Nat := [360582435322756647, 360582435519849604, 360582435817004715, 360582436046402751, 360582436189504634, 360582436332748812, 360582436491215855, 360582436701110594, 360582436945036755, 360582437189284169]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588702208564898, 360588768135921687⟩, ⟨(-635912154269675720), (-631471714885944014)⟩, true⟩

def words04 : List Nat := [360582437382971878, 360582437476553345, 360582437567360065, 360582437658570667, 360582437723960525, 360582437725411556, 360582437722356999, 360582437669079664, 360582437615520986, 360582437655877518]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360559420035300397, 360559485976309173⟩, ⟨2285174894282026038, 2289616695519506254⟩, true⟩

def words05 : List Nat := [360582437767978736, 360582437880355022, 360582437928962705, 360582437930413474, 360582437878704675, 360582437789407455, 360582437699686934, 360582437607728666, 360582437454827264, 360582437226264261]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584071799441992, 360584137754142282⟩, ⟨(-174183695014763270), (-169740527844028832)⟩, true⟩

def words06 : List Nat := [360582436997374585, 360582436869350322, 360582436811509081, 360582436819363207, 360582436820715035, 360582436742934896, 360582436589508862, 360582436536927062, 360582436483922940, 360582436452883961]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583393814355423, 360583459782884799⟩, ⟨(-106578941093929920), (-102134394126126138)⟩, true⟩

def words07 : List Nat := [360582436454199100, 360582436395322820, 360582436336172683, 360582436351361198, 360582436352582671, 360582436336092009, 360582436319443346, 360582436246314162, 360582436185377135, 360582436197291088]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573970963278808, 360574036945468585⟩, ⟨833609568273666352, 838055478344844324⟩, true⟩

def words08 : List Nat := [360582436198472393, 360582436199376309, 360582436099954785, 360582435950385355, 360582435800603310, 360582435583086392, 360582435415323391, 360582435348232918, 360582435280977976, 360582435136453101]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584465534823415, 360584531530730529⟩, ⟨(-213668528777273346), (-209221249785728006)⟩, true⟩

def words09 : List Nat := [360582435053468552, 360582435045842203, 360582435128819379, 360582435162694087, 360582435164032584, 360582435112581270, 360582435060854107, 360582435101717196, 360582435123917546, 360582435146427910]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997
