import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360543221403621602, 360543254120849119⟩, ⟨2781687398255031850, 2783260847264458962⟩, true⟩

def state01 : KState := ⟨⟨360555935538400615, 360555968265156316⟩, ⟨1876342280834324537, 1877916408298442155⟩, true⟩

def words00 : List Nat := [360582344314886756, 360582343825293392, 360582343434874527, 360582343075388629, 360582342715817383, 360582342177715025, 360582341442469375, 360582340826733300, 360582340210705944, 360582339791743853]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554922858942544, 360554955595331572⟩, ⟨1948397397962606507, 1949972211462672161⟩, true⟩

def words01 : List Nat := [360582339422330070, 360582338899741482, 360582338376974693, 360582337840921107, 360582337468943895, 360582337047301925, 360582336625570687, 360582336079169400, 360582335537894867, 360582335154605129]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360546470902101433, 360546503647999942⟩, ⟨2550352067509166766, 2551927558321445020⟩, true⟩

def words02 : List Nat := [360582334770991004, 360582334528576057, 360582334141083245, 360582333655249848, 360582333169286635, 360582332486914866, 360582331903815658, 360582331379267717, 360582330854624577, 360582330231719182]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555139550679746, 360555172306128349⟩, ⟨1932799318643477968, 1934375489756399442⟩, true⟩

def words03 : List Nat := [360582329729575602, 360582329212913214, 360582328695949441, 360582328375870415, 360582327858936835, 360582327174762385, 360582326490407030, 360582326003028425, 360582325626850168, 360582325246748175]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558224508517425, 360558257273584316⟩, ⟨1712882507595821953, 1714459363962169913⟩, true⟩

def words04 : List Nat := [360582324866506403, 360582324388011742, 360582323751641886, 360582323274598809, 360582322797291147, 360582322270410213, 360582321752746102, 360582321056684439, 360582320360448660, 360582319861148698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712A
