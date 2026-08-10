import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk583A
