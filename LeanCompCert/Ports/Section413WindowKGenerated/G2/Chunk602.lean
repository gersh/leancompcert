import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360622035852043395, 360622058930524960⟩, ⟨(-2394739651339732673), (-2393801064169056913)⟩, true⟩

def state01 : KState := ⟨⟨360595225503148637, 360595248589655538⟩, ⟨(-780793583530620038), (-779854513195620462)⟩, true⟩

def words00 : List Nat := [360582295976811961, 360582296337697005, 360582296605997990, 360582296874530370, 360582297072253056, 360582297073095697, 360582296996030631, 360582296687811105, 360582296379439971, 360582296562398133]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596496055477555, 360596519149919640⟩, ⟨(-857223753886835248), (-856284205734048132)⟩, true⟩

def words01 : List Nat := [360582296897343281, 360582297232437422, 360582297428761044, 360582297873320791, 360582298247207019, 360582298621308719, 360582299270974097, 360582299646043885, 360582299882927454, 360582300119917913]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608360402468845, 360608383504877390⟩, ⟨(-1571744815251901056), (-1570804787320304010)⟩, true⟩

def words02 : List Nat := [360582300346601743, 360582300711019799, 360582301350960439, 360582301991041468, 360582302365291018, 360582302464920584, 360582302781364800, 360582303098070787, 360582303397954191, 360582303831829951]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577514756857878, 360577537867286598⟩, ⟨286234737267758906, 287175248294287376⟩, true⟩

def words03 : List Nat := [360582304073408824, 360582304315069926, 360582304571739871, 360582304966068840, 360582305173521089, 360582305381098048, 360582305392884920, 360582305393728054, 360582305130859637, 360582305052683250]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586033928814887, 360586057047196283⟩, ⟨(-226931042102243824), (-225990051966907792)⟩, true⟩

def words04 : List Nat := [360582305108013291, 360582305366387176, 360582305467021017, 360582305567743535, 360582305597860377, 360582305768421095, 360582305980031701, 360582306191794669, 360582306192560443, 360582306237218575]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360635707754151009, 360635730880488778⟩, ⟨(-3220084758810721806), (-3219143289265291966)⟩, true⟩

def words05 : List Nat := [360582306575674968, 360582306914367646, 360582307463214419, 360582307830369101, 360582307956038158, 360582308081772617, 360582308482794489, 360582309094813134, 360582309982016358, 360582310869382669]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601435456288288, 360601458590673049⟩, ⟨(-1154792371332307984), (-1153850416838019542)⟩, true⟩

def words06 : List Nat := [360582311596650134, 360582312177044523, 360582312749157428, 360582313321497343, 360582313731530945, 360582313867367504, 360582313868118845, 360582313865465938, 360582313900514406, 360582314219137186]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557385285526486, 360557408427843704⟩, ⟨1500453593717870598, 1501396026341930184⟩, true⟩

def words07 : List Nat := [360582314812800897, 360582315406606639, 360582315822732832, 360582315964665271, 360582316037419541, 360582316110394231, 360582316129089821, 360582316129933489, 360582315874439478, 360582315462122768]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583374064771501, 360583397215047070⟩, ⟨(-66300375100176086), (-65357462706788424)⟩, true⟩

def words08 : List Nat := [360582315049625848, 360582314717922781, 360582314573369194, 360582314555962563, 360582314538476038, 360582314288337175, 360582313866844381, 360582313540782530, 360582313214483879, 360582313181564349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588904117829615, 360588927276161632⟩, ⟨(-399777106548701636), (-398833708394500074)⟩, true⟩

def words09 : List Nat := [360582313182342706, 360582312928586621, 360582312695263458, 360582312891811636, 360582312975082535, 360582313058487985, 360582313059239733, 360582313007130749, 360582313117504162, 360582313228162520]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602
