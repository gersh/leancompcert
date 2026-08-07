import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492221337081288, 362492261638062995⟩, ⟨(-382118644553796704), (-380683838630099622)⟩, true⟩

def state01 : KState := ⟨⟨362480161816500824, 362480202133446123⟩, ⟨253386510521837859, 254822157806882263⟩, true⟩

def words00 : List Nat := [371285038242664151, 371285038244438465, 371285037969647944, 371285037844505676, 371285037718448823, 371285037682339853, 371285037309062974, 371285036936776169, 371285036563802207, 371285036551162058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458665392063775, 362458705724916238⟩, ⟨1386679031962806557, 1388115517796884255⟩, true⟩

def words01 : List Nat := [371285036728393961, 371285036998077254, 371285037266447975, 371285037268214368, 371285037057156762, 371285036910076140, 371285036762127398, 371285036681340353, 371285036182852788, 371285035685420732]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477152978328368, 362477193326995198⟩, ⟨411973115320198335, 413410434967152301⟩, true⟩

def words02 : List Nat := [371285035187199104, 371285035049113104, 371285034766513658, 371285034668239318, 371285034569407537, 371285034404622661, 371285033823732806, 371285033603082473, 371285033462374202, 371285033464202996]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491794389809858, 362491834754596696⟩, ⟨(-360126736633005725), (-358688566898310909)⟩, true⟩

def words03 : List Nat := [371285033316880692, 371285033119336075, 371285033080870387, 371285033156989998, 371285033329216675, 371285033502137553, 371285033674747404, 371285033676545389, 371285033679846731, 371285033810987392]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474786630778254, 362474827011285256⟩, ⟨536950579314504753, 538389578213400879⟩, true⟩

def words04 : List Nat := [371285034180070262, 371285034181837673, 371285034072199083, 371285033963557259, 371285033854254458, 371285033692564012, 371285033389538270, 371285033418822646, 371285033446955049, 371285033448786932]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494630660724575, 362494671057261623⟩, ⟨(-509919536498395754), (-508479691934768178)⟩, true⟩

def words05 : List Nat := [371285033256507942, 371285033201554152, 371285033401706292, 371285033403482504, 371285033317125414, 371285033171538346, 371285033236624800, 371285033272960559, 371285033456853660, 371285033641520171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490455339002732, 362490495751492646⟩, ⟨(-289657958604015132), (-288217272285189458)⟩, true⟩

def words06 : List Nat := [371285033810072497, 371285033811845385, 371285033830074033, 371285033973861003, 371285034194089564, 371285034195888519, 371285034118286940, 371285033955424354, 371285033985741166, 371285034091257192]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483988696110405, 362484029124532740⟩, ⟨51674664758740953, 53116191911619863⟩, true⟩

def words07 : List Nat := [371285034534077487, 371285034977583365, 371285035344816998, 371285035346585534, 371285035235451720, 371285035232198138, 371285035528634367, 371285035530414907, 371285035511269235, 371285035494216553]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485906703055460, 362485947147293062⟩, ⟨(-49455714636644804), (-48013352672102836)⟩, true⟩

def words08 : List Nat := [371285035763385241, 371285035917611861, 371285036429580546, 371285036942271393, 371285037336381508, 371285037338150572, 371285037316987502, 371285037382024201, 371285037629404375, 371285037648464245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483769359633930, 362483809820015933⟩, ⟨63414744348214688, 64857958654550962⟩, true⟩

def words09 : List Nat := [371285037667359035, 371285037686865016, 371285037886514615, 371285037958928475, 371285038140721494, 371285038323168480, 371285038505393947, 371285038507163404, 371285038211474842, 371285038190444997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527
