import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573323359357815, 360573331551038022⟩, ⟨308835086081959350, 309037762189648584⟩, true⟩

def state01 : KState := ⟨⟨360573521008283973, 360573529204607785⟩, ⟨301405241412137829, 301608087499542293⟩, true⟩

def words00 : List Nat := [360581774994199107, 360581774994691696, 360581774269291226, 360581772974219935, 360581771679138993, 360581770193960947, 360581769083448172, 360581768718225210, 360581768352962738, 360581767611805260]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559931286985872, 360559939487956997⟩, ⟨798953900509881956, 799156916758768348⟩, true⟩

def words01 : List Nat := [360581767603148132, 360581767819654216, 360581767983091385, 360581767983584133, 360581767402873542, 360581766192214883, 360581764981534197, 360581763749297574, 360581763046712909, 360581762451276461]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360538197479865496, 360538205685532903⟩, ⟨1594647505155324694, 1594850693404381322⟩, true⟩

def words02 : List Nat := [360581761855807596, 360581760780489800, 360581758961129110, 360581757649668633, 360581756338140499, 360581754826847747, 360581752571657733, 360581749850568051, 360581747129532574, 360581745153002311]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360508656476253465, 360508664686566207⟩, ⟨2676863921037614991, 2677067279468846807⟩, true⟩

def words03 : List Nat := [360581743964811551, 360581742755320865, 360581741545841276, 360581739961051639, 360581738175441910, 360581735938751641, 360581733702038857, 360581732209416866, 360581730743521227, 360581728749870488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360543777706032124, 360543785920995758⟩, ⟨1389852705927899321, 1390056234791177601⟩, true⟩

def words04 : List Nat := [360581726756219692, 360581724870105814, 360581723391161817, 360581722656018601, 360581721920884710, 360581720464032581, 360581718502807757, 360581716762205703, 360581715021549286, 360581713785519392]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366
