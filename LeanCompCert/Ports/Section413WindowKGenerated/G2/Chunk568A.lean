import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575003840401946, 360575024290473083⟩, ⟨385028200489068375, 385812979498927533⟩, true⟩

def state01 : KState := ⟨⟨360623722230383072, 360623742687922599⟩, ⟨(-2382482294126705875), (-2381697090875581987)⟩, true⟩

def words00 : List Nat := [360581816763767428, 360581817029280568, 360581817492741650, 360581817956343083, 360581818120682449, 360581818121473849, 360581818141383347, 360581818306671887, 360581818781254818, 360581819520034768]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602936431984709, 360602956897065487⟩, ⟨(-1201455949069821084), (-1200670317362465608)⟩, true⟩

def words01 : List Nat := [360581820070524603, 360581820621094635, 360581821480996416, 360581822565119513, 360581823448516300, 360581824332007078, 360581825021398920, 360581825402219644, 360581825774773103, 360581826147565083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615398368174385, 360615418840711299⟩, ⟨(-1909644621858584916), (-1908858566456996736)⟩, true⟩

def words02 : List Nat := [360581826829520232, 360581827202998135, 360581827363080029, 360581827523238691, 360581827603242372, 360581827996940164, 360581828699739507, 360581829402665791, 360581829915618404, 360581830507469636]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612395287793620, 360612415767814737⟩, ⟨(-1739055841789999621), (-1738269361023717903)⟩, true⟩

def words03 : List Nat := [360581831201617255, 360581831895971497, 360581832482286397, 360581832835108162, 360581832922174568, 360581833009295943, 360581833142869462, 360581833430953355, 360581833969636109, 360581834508494463]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600086848102285, 360600107335663480⟩, ⟨(-1039479305279389064), (-1038692395897483540)⟩, true⟩

def words04 : List Nat := [360581834891683667, 360581835056622417, 360581835530595391, 360581836004792158, 360581836400117651, 360581836600486832, 360581836601204608, 360581836563925602, 360581836580213991, 360581836902497881]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568A
