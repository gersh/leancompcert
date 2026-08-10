import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk366A
