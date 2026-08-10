import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591A

def state06 : KState := ⟨⟨360608321968812358, 360608344226001237⟩, ⟨(-1558325741763334769), (-1557436170649916357)⟩, true⟩

def words05 : List Nat := [360582015753238546, 360582015888100771, 360582016242611881, 360582016739368219, 360582017162649267, 360582017586052262, 360582017788227392, 360582017948238795, 360582018393908273, 360582018839840593]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606981198961599, 360607003463933559⟩, ⟨(-1479061909382077183), (-1478171877782922311)⟩, true⟩

def words06 : List Nat := [360582019486435770, 360582019848398453, 360582019973764527, 360582020099226985, 360582020151374737, 360582020377994786, 360582020890090007, 360582021402326776, 360582021683834947, 360582022106887322]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599319661387984, 360599341934176945⟩, ⟨(-1025745811259067994), (-1024855317089601740)⟩, true⟩

def words07 : List Nat := [360582022469469382, 360582022832270211, 360582023387305639, 360582023657792099, 360582023682101443, 360582023706470512, 360582023762647542, 360582024044254268, 360582024337554990, 360582024631037600]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573160024147063, 360573182304801370⟩, ⟨522438228636617364, 523329188316627486⟩, true⟩

def words08 : List Nat := [360582024780611971, 360582024781439060, 360582024942967995, 360582025167108105, 360582025167813681, 360582025157787773, 360582024940743567, 360582024576978305, 360582024213070572, 360582023818373201]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360544386343956401, 360544408632406384⟩, ⟨2225751454422157330, 2226642875568567246⟩, true⟩

def words09 : List Nat := [360582023669673797, 360582023563096889, 360582023456425383, 360582023207262590, 360582022862358065, 360582022444663323, 360582022026739877, 360582021894447595, 360582021477636652, 360582020843142340]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591B
