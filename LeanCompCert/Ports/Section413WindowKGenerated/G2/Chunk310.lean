import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360519882021505222, 360519887817780987⟩, ⟨1956155930248652190, 1956277442548875722⟩, true⟩

def state01 : KState := ⟨⟨360547582618716618, 360547588418887197⟩, ⟨1097236162170879124, 1097357795229307742⟩, true⟩

def words00 : List Nat := [360582991506464851, 360582990028307359, 360582989075662644, 360582987781117444, 360582986486628372, 360582984283245048, 360582981532229337, 360582979515136279, 360582977498052958, 360582975642209652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569681442679835, 360569687246772161⟩, ⟨411805979918394508, 411927734609930980⟩, true⟩

def words01 : List Nat := [360582974501458401, 360582972844794771, 360582971188159252, 360582970567034923, 360582970464830127, 360582970099437971, 360582969734030857, 360582968561231568, 360582967098474124, 360582966670840825]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360533444456142331, 360533450264112033⟩, ⟨1535997128175105998, 1536119003162532658⟩, true⟩

def words02 : List Nat := [360582966538655038, 360582966539067225, 360582965798620320, 360582964519200094, 360582963239789478, 360582961281922402, 360582959848663719, 360582958264984253, 360582956681361938, 360582954582615499]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567856442688361, 360567862254554723⟩, ⟨467721988019851917, 467843983940108521⟩, true⟩

def words03 : List Nat := [360582952987640665, 360582950558146518, 360582948128684257, 360582946733377088, 360582944705829796, 360582941788247118, 360582938870773809, 360582936551936759, 360582935033017035, 360582934547851763]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586510192445534, 360586516008244537⟩, ⟨(-111572333261214741), (-111450215253791869)⟩, true⟩

def words04 : List Nat := [360582934062661838, 360582933047006363, 360582932418111844, 360582932372148645, 360582932326083253, 360582931565343480, 360582930612393526, 360582929046654196, 360582927480936960, 360582926744927614]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360510699521096519, 360510705340786099⟩, ⟨2242943356702646003, 2243065595532257619⟩, true⟩

def words05 : List Nat := [360582927893648935, 360582929042382213, 360582929390524511, 360582929390937222, 360582928704598025, 360582927755827713, 360582926806999457, 360582926164811868, 360582924845028590, 360582922520294543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633178156258972, 360633183979844903⟩, ⟨(-1561909037817649354), (-1561786677947994300)⟩, true⟩

def words06 : List Nat := [360582920195617071, 360582918612388675, 360582917684913658, 360582917737417993, 360582917737799433, 360582916970536895, 360582916263318637, 360582916255065862, 360582917269472031, 360582918887702778]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598980985105295, 360598986812628004⟩, ⟨(-499345674288172649), (-499223192083492115)⟩, true⟩

def words07 : List Nat := [360582919991497582, 360582921095266388, 360582921831846024, 360582923091956572, 360582923663755900, 360582924235584142, 360582924286411868, 360582924286825092, 360582924289881283, 360582924807155739]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583694294566280, 360583700125977493⟩, ⟨(-24156228229182170), (-24033625149991032)⟩, true⟩

def words08 : List Nat := [360582926355088578, 360582926870456906, 360582926870826688, 360582926717769556, 360582926564654123, 360582926563395961, 360582926949775853, 360582927336204525, 360582927336572838, 360582927116902520]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630567437147357, 360630573272458637⟩, ⟨(-1481713696904347870), (-1481590972552646806)⟩, true⟩

def words09 : List Nat := [360582928172319982, 360582929227790379, 360582930130632825, 360582931071794271, 360582931143764582, 360582931215761538, 360582931375922554, 360582932158716497, 360582933690919455, 360582935223117695]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310
