import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk303

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480091283974952, 362480104016071139⟩, ⟨166646923220361696, 166907690008099656⟩, true⟩

def state01 : KState := ⟨⟨362464299116364428, 362464311857128999⟩, ⟨645233887931508065, 645494917416601767⟩, true⟩

def words00 : List Nat := [371285613135535098, 371285613136507296, 371285612641333849, 371285611894649539, 371285611147636527, 371285610359892511, 371285609026800414, 371285608781123453, 371285608535144251, 371285608291223906]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505684841216417, 362505697590781512⟩, ⟨(-609368750140136902), (-609107453867069690)⟩, true⟩

def words01 : List Nat := [371285607589288519, 371285607576313546, 371285608635089815, 371285608636063780, 371285608542035401, 371285608280266876, 371285608052902113, 371285608053974481, 371285608293704727, 371285608957363516]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472042692138663, 362472055450488540⟩, ⟨410774236742197598, 411035799414562136⟩, true⟩

def words02 : List Nat := [371285609633290710, 371285609634263739, 371285609175667737, 371285609490136620, 371285610128227626, 371285610129200916, 371285609477725705, 371285608604632589, 371285607731194273, 371285607570482426]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465395245794216, 362465408012905661⟩, ⟨612450352344629617, 612712180800220533⟩, true⟩

def words03 : List Nat := [371285607124347368, 371285607121624398, 371285607118582901, 371285607117655958, 371285605946874809, 371285605106456532, 371285604265577803, 371285604197248087, 371285603541693552, 371285602877137706]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478999989177931, 362479012764999287⟩, ⟨199789446277479538, 200051539036579486⟩, true⟩

def words04 : List Nat := [371285602631123905, 371285602642752807, 371285603450270517, 371285604258137039, 371285604681661414, 371285604682635203, 371285603722093092, 371285603784670455, 371285604247978413, 371285604248987313]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362469400713570558, 362469413498283343⟩, ⟨491261122975977032, 491523485633755158⟩, true⟩

def words05 : List Nat := [371285604032540711, 371285603700616359, 371285603971213329, 371285604031957980, 371285604307659065, 371285604583701974, 371285604850840000, 371285604851814460, 371285603868469757, 371285603336413573]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480734759530681, 362480747552922997⟩, ⟨147190422766968535, 147453048980013601⟩, true⟩

def words06 : List Nat := [371285603164865419, 371285603165844637, 371285602794667530, 371285602321568591, 371285601848137522, 371285601704610093, 371285601701227998, 371285602241569807, 371285602772493470, 371285602773501859]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492621357059230, 362492634159253381⟩, ⟨(-213909730051411333), (-213646836481926407)⟩, true⟩

def words07 : List Nat := [371285602969464863, 371285603325756370, 371285604132262857, 371285604133237464, 371285603497035801, 371285602689145268, 371285601896981671, 371285601898055491, 371285601675051804, 371285601907632897]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462317540775394, 362462330351763227⟩, ⟨706785587544500846, 707048748311328998⟩, true⟩

def words08 : List Nat := [371285602045068847, 371285602046050310, 371285601213385362, 371285601152921510, 371285601181150814, 371285601182125866, 371285599830578167, 371285598255921872, 371285596680982457, 371285596187508911]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466421199637312, 362466434019418069⟩, ⟨582226487029928626, 582489915057486214⟩, true⟩

def words09 : List Nat := [371285595737933615, 371285596054292706, 371285596163515358, 371285596164512225, 371285595664656558, 371285595494166251, 371285596131501902, 371285596132477520, 371285595501086202, 371285594871887066]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk303
