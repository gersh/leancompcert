import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk753A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545246391342183, 360545283147849490⟩, ⟨2781585298556102983, 2783454707501354025⟩, true⟩

def state01 : KState := ⟨⟨360565797273984655, 360565834040591092⟩, ⟨1233967828093549859, 1235837997553626463⟩, true⟩

def words00 : List Nat := [360582247527775246, 360582247185361991, 360582246760253769, 360582246247352617, 360582245734290392, 360582245176928362, 360582244791563810, 360582244582539842, 360582244373409052, 360582244052509213]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560701695096349, 360560738471834941⟩, ⟨1617699007477157375, 1619569940040405291⟩, true⟩

def words01 : List Nat := [360582243835479745, 360582243755021985, 360582243674257041, 360582243518840001, 360582243187148504, 360582242705661876, 360582242223986715, 360582241706841084, 360582241277965683, 360582240993609243]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360554566246222388, 360554603033184910⟩, ⟨2079768170365077144, 2081639873043322852⟩, true⟩

def words02 : List Nat := [360582240709095497, 360582240335900000, 360582239910284300, 360582239661050438, 360582239411541415, 360582239058760594, 360582238529758745, 360582237842364951, 360582237154776782, 360582236643606301]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541144304595652, 360541181101655893⟩, ⟨3090978975460445678, 3092851438850808702⟩, true⟩

def words03 : List Nat := [360582236277644571, 360582236038893821, 360582235800032062, 360582235473100326, 360582235151591585, 360582234700276254, 360582234248657593, 360582233973241703, 360582233562601495, 360582233018816111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567544308606132, 360567581115815714⟩, ⟨1101793137311792855, 1103666365400899987⟩, true⟩

def words04 : List Nat := [360582232474817547, 360582231888341282, 360582231411327978, 360582231052216772, 360582230693029006, 360582230184189603, 360582229549108287, 360582229090343567, 360582228631237012, 360582228313763968]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk753A
