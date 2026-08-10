import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511657896265915, 362511701610250126⟩, ⟨(-1469996512663847236), (-1468378232473819996)⟩, true⟩

def state01 : KState := ⟨⟨362499382219636168, 362499425950284419⟩, ⟨(-797268608572866226), (-795649415111658044)⟩, true⟩

def words00 : List Nat := [371284907365221420, 371284907626253859, 371284908024815685, 371284908424274980, 371284908894253907, 371284908972632798, 371284909051107248, 371284909130233148, 371284909447208552, 371284909714216629]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469061817087728, 362469105564287694⟩, ⟨864834672221512213, 866454772968668979⟩, true⟩

def words01 : List Nat := [371284910248302372, 371284910783100924, 371284911242138288, 371284911258329997, 371284911342502150, 371284911427605309, 371284911584755763, 371284911586598779, 371284911300628425, 371284911014360089]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485140382742160, 362485184146436177⟩, ⟨(-16646165339676325), (-15025160304251157)⟩, true⟩

def words02 : List Nat := [371284910727306554, 371284910662068536, 371284910493632745, 371284910559799655, 371284910561232264, 371284910542393852, 371284910122343680, 371284910009457079, 371284910112788282, 371284910119693929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489420734596590, 362489464515126368⟩, ⟨(-251336690927188189), (-249714762701920177)⟩, true⟩

def words03 : List Nat := [371284910121096612, 371284910058819430, 371284910263690941, 371284910437979999, 371284910623563933, 371284910809820964, 371284910999560350, 371284911001436137, 371284910997825004, 371284911083155728]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481099047020931, 362481142843970591⟩, ⟨205117214323841891, 206740043101503161⟩, true⟩

def words04 : List Nat := [371284911471343262, 371284911521185328, 371284911553924982, 371284911587268563, 371284911635351217, 371284911637415728, 371284911730806381, 371284911889319770, 371284912031541929, 371284912033452843]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548A
