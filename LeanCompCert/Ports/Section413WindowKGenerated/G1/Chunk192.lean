import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk192

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488294992756322, 362488299910797206⟩, ⟨(-47655817452035345), (-47591951091246815)⟩, true⟩

def state01 : KState := ⟨⟨362438074192257504, 362438079115595546⟩, ⟨916701631629833029, 916765599723609411⟩, true⟩

def words00 : List Nat := [371285822030262163, 371285822030856043, 371285819165146052, 371285816010328778, 371285812855619530, 371285809940269883, 371285806084578926, 371285804925996986, 371285803767320456, 371285802468001773]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362531124574395871, 362531129503092283⟩, ⟨(-871182768517712468), (-871118697461632076)⟩, true⟩

def words01 : List Nat := [371285800195991534, 371285800408427012, 371285803315925124, 371285803667360561, 371285803667832723, 371285803285874152, 371285803925453684, 371285803926108067, 371285805948972614, 371285808307656998]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461460946450659, 362461465880519488⟩, ⟨468154996425191729, 468219170766248613⟩, true⟩

def words02 : List Nat := [371285810443633851, 371285810444238589, 371285812444345656, 371285814557219399, 371285817472374833, 371285817472969441, 371285816792402611, 371285815817803403, 371285814843070910, 371285814251334166]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441850631674747, 362441855571104332⟩, ⟨845645744991269580, 845710022447092734⟩, true⟩

def words03 : List Nat := [371285814410478062, 371285815835822907, 371285817245666245, 371285817246261423, 371285815511056426, 371285814605903389, 371285815484211023, 371285815484806255, 371285813677525313, 371285811393476843]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479977227497602, 362479982172262309⟩, ⟨111897616163445365, 111961996294383787⟩, true⟩

def words04 : List Nat := [371285809117960198, 371285809118621507, 371285807788258824, 371285807593012747, 371285807397605853, 371285806751696144, 371285802517656284, 371285800243188362, 371285798379230603, 371285798379862018]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473486308365270, 362473491258542546⟩, ⟨236930918740572502, 236995403091286416⟩, true⟩

def words05 : List Nat := [371285798078187821, 371285797626284546, 371285798482660137, 371285798483315742, 371285799226167278, 371285800012356621, 371285800274530091, 371285800275125679, 371285796954005193, 371285796315816237]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362441996150551519, 362442001106034974⟩, ⟨843451896775568192, 843516483350348178⟩, true⟩

def words06 : List Nat := [371285795677365925, 371285795502670931, 371285791745767234, 371285788002988539, 371285784260351503, 371285781347736714, 371285777669700158, 371285776672199957, 371285775674612373, 371285774665108682]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509322037943631, 362509326998829650⟩, ⟨(-454285346346513958), (-454220655637804010)⟩, true⟩

def words07 : List Nat := [371285772394047287, 371285771258666198, 371285771665355835, 371285771665952648, 371285770351446392, 371285768597649200, 371285767148955425, 371285767149631403, 371285767835516290, 371285769058077729]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362447578853969871, 362447583820222149⟩, ⟨736241340153268261, 736306134352051245⟩, true⟩

def words08 : List Nat := [371285770294294802, 371285770294891409, 371285768541318319, 371285768186122449, 371285767830685218, 371285767428375985, 371285763453667083, 371285759469288542, 371285755485076452, 371285754174517227]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362399147779981032, 362399152751611597⟩, ⟨1671015260434574051, 1671080158407218843⟩, true⟩

def words09 : List Nat := [371285752467252831, 371285752738872061, 371285752814488979, 371285752815089646, 371285750486566367, 371285748230736966, 371285745974819341, 371285745622236528, 371285741701587088, 371285737215777775]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk192
