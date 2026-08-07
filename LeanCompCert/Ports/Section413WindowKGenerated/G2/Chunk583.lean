import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555229459901375, 360555251049482431⟩, ⟨1558273033059276598, 1559123394850768044⟩, true⟩

def state01 : KState := ⟨⟨360593439750840729, 360593461348112574⟩, ⟨(-669649218346272980), (-668798408145559106)⟩, true⟩

def words00 : List Nat := [360581993702836940, 360581993476980034, 360581993442441331, 360581993399961058, 360581993357423333, 360581993041056445, 360581992431199624, 360581992071046416, 360581991710666352, 360581991841361780]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590857574547576, 360590879179577294⟩, ⟨(-519076486181711683), (-518225223581086513)⟩, true⟩

def words01 : List Nat := [360581991842100808, 360581991809236022, 360581992036671166, 360581992444821826, 360581992750258674, 360581993055818093, 360581993136888363, 360581993137706526, 360581993286602451, 360581993439902373]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601312495849166, 360601334108543440⟩, ⟨(-1128829721370212210), (-1127978011733252798)⟩, true⟩

def words02 : List Nat := [360581993886984112, 360581994306041147, 360581994576819319, 360581994847691333, 360581995041990630, 360581995383170701, 360581995716492931, 360581996049958902, 360581996236762065, 360581996569126437]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608585273543811, 360608606893933108⟩, ⟨(-1553254695051382691), (-1552402536524484005)⟩, true⟩

def words03 : List Nat := [360581996778944257, 360581996988979246, 360581997242603022, 360581997243417537, 360581997204070323, 360581996916314652, 360581996633784869, 360581996862493939, 360581997319272289, 360581997776219588]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576716317655924, 360576737945802589⟩, ⟨306056572556451731, 306909183685629739⟩, true⟩

def words04 : List Nat := [360581998084931335, 360581998221382445, 360581998526128432, 360581998831115424, 360581998937259813, 360581998938074511, 360581998751324326, 360581998416190489, 360581998080913203, 360581997743295060]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360514244044408242, 360514265680236388⟩, ⟨3951693171153138560, 3952546230535449612⟩, true⟩

def words05 : List Nat := [360581997653814403, 360581997559665675, 360581997465417260, 360581997201190415, 360581996720769925, 360581996050857717, 360581995380724375, 360581994743991593, 360581993814394157, 360581992654714378]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585917912122002, 360585939555640559⟩, ⟨(-231623750672484614), (-230770242438787604)⟩, true⟩

def words06 : List Nat := [360581991494891514, 360581990432090740, 360581989549707088, 360581988961184618, 360581988372625736, 360581987533286749, 360581986851049669, 360581986462721576, 360581986074165832, 360581986047178501]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578767530315691, 360578789181606622⟩, ⟨185718680898783472, 186572642842889924⟩, true⟩

def words07 : List Nat := [360581986047904467, 360581985968485040, 360581985888924189, 360581985774615460, 360581985775298295, 360581985743357725, 360581985711334924, 360581985414535753, 360581985066901624, 360581985013104445]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560218935236895, 360560240594197885⟩, ⟨1268668733780730465, 1269523143542163813⟩, true⟩

def words08 : List Nat := [360581985121038944, 360581985121854147, 360581984991965253, 360581984675342617, 360581984358597387, 360581983966832128, 360581983768902106, 360581983470934941, 360581983172883483, 360581982727158018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602823333721123, 360602845000377666⟩, ⟨(-1219158065763077887), (-1218303206619864069)⟩, true⟩

def words09 : List Nat := [360581982355462962, 360581982277438494, 360581982413643734, 360581982738412359, 360581982770833734, 360581982803319520, 360581982971030809, 360581983285369919, 360581983643254772, 360581984001308817]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583
