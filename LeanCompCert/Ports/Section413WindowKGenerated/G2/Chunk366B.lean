import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366A

def state06 : KState := ⟨⟨360524111460077701, 360524119679744847⟩, ⟨2110837298898298080, 2111041000167735568⟩, true⟩

def words05 : List Nat := [360581712751121156, 360581711266235172, 360581709781322484, 360581709039825140, 360581708793562048, 360581708357660420, 360581707921732202, 360581707114850397, 360581705565324214, 360581703995079483]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360534160689692313, 360534168914004694⟩, ⟨1742330429532558043, 1742534301119019467⟩, true⟩

def words06 : List Nat := [360581702424754389, 360581701357391694, 360581699962124993, 360581697958441183, 360581695954786113, 360581693762021982, 360581692200923844, 360581691059340478, 360581689917766524, 360581688256822230]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576807238253642, 360576815467228080⟩, ⟨178181270453387328, 178385313020747520⟩, true⟩

def words07 : List Nat := [360581686961392308, 360581686408524665, 360581685855551765, 360581684910409755, 360581683854619862, 360581682147527695, 360581680440433988, 360581679475722686, 360581678884823010, 360581678752752092]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360558111996275447, 360558120229948708⟩, ⟨863805920711911058, 864010135655502912⟩, true⟩

def words08 : List Nat := [360581678620608416, 360581678114040817, 360581676865844576, 360581676359738566, 360581675853528263, 360581674647053859, 360581673620341328, 360581672026261785, 360581670432175438, 360581669157058425]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551050681352811, 360551058919673477⟩, ⟨1123066726228627553, 1123271111708986321⟩, true⟩

def words09 : List Nat := [360581668615406641, 360581668715661535, 360581668716105811, 360581668414804660, 360581668139635354, 360581667497742913, 360581666954747102, 360581666955241088, 360581666595439295, 360581665761954376]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366B
