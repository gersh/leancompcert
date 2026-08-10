import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592141723262586, 360592204867376102⟩, ⟨(-960125685761960245), (-955960032479068167)⟩, true⟩

def state01 : KState := ⟨⟨360600935152247057, 360600998309870002⟩, ⟨(-1819375856962108588), (-1815208883740801756)⟩, true⟩

def words00 : List Nat := [360582420358225284, 360582420380297550, 360582420464892702, 360582420549919702, 360582420608053926, 360582420671438170, 360582420682120975, 360582420692965241, 360582420794345319, 360582420986091300]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573764945964094, 360573828116965960⟩, ⟨835621663403584244, 839789943944992828⟩, true⟩

def words01 : List Nat := [360582421282053187, 360582421578282174, 360582421776460720, 360582421870332400, 360582421937490616, 360582422005028105, 360582422075144351, 360582422076563456, 360582422042383510, 360582421955933879]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586003998540430, 360586067182930487⟩, ⟨(-360445608864596567), (-356276019962866449)⟩, true⟩

def words02 : List Nat := [360582421869143899, 360582421821333830, 360582421909325968, 360582421997597897, 360582421998908263, 360582421998054807, 360582421916157060, 360582421799247824, 360582421681924152, 360582421706879256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577254028694250, 360577317226615427⟩, ⟨494740725781342521, 498911637145335243⟩, true⟩

def words03 : List Nat := [360582421708155487, 360582421694444003, 360582421701045242, 360582421807574184, 360582421846288772, 360582421885229215, 360582421886493635, 360582421872950678, 360582421754769400, 360582421704179836]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568616384844140, 360568679596152390⟩, ⟨1338955042402808938, 1343127262285172070⟩, true⟩

def words04 : List Nat := [360582421653122712, 360582421599895767, 360582421442153258, 360582421227043289, 360582421011705562, 360582420761106408, 360582420590396131, 360582420420604354, 360582420250648191, 360582420028503134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977A
