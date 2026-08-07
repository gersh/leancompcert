import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586645501706619, 360586703650622588⟩, ⟨(-440239506953881477), (-436552460710165305)⟩, true⟩

def state01 : KState := ⟨⟨360583551719283456, 360583609880994400⟩, ⟨(-149701740126719090), (-146013492370435774)⟩, true⟩

def words00 : List Nat := [360582054743079923, 360582054845467126, 360582054888982823, 360582054932646063, 360582054933803756, 360582054943027776, 360582055004747983, 360582055066723845, 360582055067936953, 360582055073864560]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597803406841513, 360597861581406119⟩, ⟨(-1488130135673966973), (-1484440680766451567)⟩, true⟩

def words01 : List Nat := [360582055204826040, 360582055336218200, 360582055580478068, 360582055711929372, 360582055746317406, 360582055780799134, 360582055864669125, 360582056037075003, 360582056206480713, 360582056376172291]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591787095737202, 360591845283248703⟩, ⟨(-923114442482667517), (-919423771539596517)⟩, true⟩

def words02 : List Nat := [360582056488804246, 360582056514264694, 360582056652739806, 360582056791625601, 360582056844264128, 360582056899825779, 360582056901037351, 360582056891677233, 360582056888514288, 360582056994275525]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575469046527908, 360575527246869868⟩, ⟨609708815005396941, 613400691174443355⟩, true⟩

def words03 : List Nat := [360582057106686081, 360582057219355514, 360582057239407049, 360582057240767442, 360582057181111549, 360582057093284803, 360582057028976172, 360582057030342890, 360582057022103236, 360582056954035873]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595598350500431, 360595656563661685⟩, ⟨(-1281309916611455744), (-1277616836132812822)⟩, true⟩

def words04 : List Nat := [360582056929358593, 360582057054626115, 360582057245165432, 360582057435960994, 360582057530380519, 360582057536597414, 360582057539979431, 360582057543741862, 360582057660323759, 360582057806478337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584075083729934, 360584133309863013⟩, ⟨(-198633311579935305), (-194939012336944821)⟩, true⟩

def words05 : List Nat := [360582057859798730, 360582057913240865, 360582058043185731, 360582058261652220, 360582058392646986, 360582058523856717, 360582058598081952, 360582058599442586, 360582058606161173, 360582058629811322]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584403974409042, 360584462213365879⟩, ⟨(-229581166679517981), (-225885662450359493)⟩, true⟩

def words06 : List Nat := [360582058630931121, 360582058626253415, 360582058603595876, 360582058524275669, 360582058444728485, 360582058337040994, 360582058345757120, 360582058407533123, 360582058408756945, 360582058432811769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602920597879017, 360602978849680095⟩, ⟨(-1969711382505094160), (-1966014671240530968)⟩, true⟩

def words07 : List Nat := [360582058572652311, 360582058712890371, 360582058869912474, 360582058977253777, 360582058978532022, 360582058979288586, 360582059012945269, 360582059123921447, 360582059347618913, 360582059571621333]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595555359286840, 360595613624060632⟩, ⟨(-1277496294941316086), (-1273798364437325692)⟩, true⟩

def words08 : List Nat := [360582059738637020, 360582059918175993, 360582060210556714, 360582060503341337, 360582060767260248, 360582060918540708, 360582061002143890, 360582061085881145, 360582061134316403, 360582061280065598]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576642725977074, 360576701003564991⟩, ⟨500223152995349140, 503922287962423732⟩, true⟩

def words09 : List Nat := [360582061520446432, 360582061761084200, 360582061906544672, 360582061939306919, 360582061940453563, 360582061900693797, 360582061932293347, 360582061933655000, 360582061934588774, 360582061878968847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939
