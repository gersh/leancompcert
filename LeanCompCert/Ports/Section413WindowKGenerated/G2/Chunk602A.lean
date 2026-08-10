import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk602A
