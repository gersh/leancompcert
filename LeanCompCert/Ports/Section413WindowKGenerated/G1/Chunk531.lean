import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk531

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487022685174517, 362487063625258707⟩, ⟨(-111228804352968064), (-109760189672131628)⟩, true⟩

def state01 : KState := ⟨⟨362485340270545707, 362485381226516093⟩, ⟨(-21816173094497982), (-20346714775052868)⟩, true⟩

def words00 : List Nat := [371284997011639494, 371284997111753841, 371284997208108633, 371284997305082173, 371284997453366400, 371284997455328866, 371284997693071266, 371284997939558467, 371284998119517259, 371284998128574517]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362514404913876978, 362514445885962251⟩, ⟨(-1565560274738714212), (-1564089960476320286)⟩, true⟩

def words01 : List Nat := [371284998456300997, 371284998784952564, 371284999466683049, 371284999676869462, 371284999828955389, 371284999981606849, 371285000487499543, 371285000863790127, 371285001419318408, 371285001975635331]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492519017633002, 362492560005801597⟩, ⟨(-402974314664157514), (-401503145974927474)⟩, true⟩

def words02 : List Nat := [371285002531163214, 371285002615162957, 371285002845961797, 371285003077638082, 371285003340596689, 371285003342378063, 371285003170168490, 371285002999292006, 371285003008687133, 371285003153004268]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469943276587167, 362469984280765839⟩, ⟨796656998609071922, 798129017994235462⟩, true⟩

def words03 : List Nat := [371285003460724625, 371285003769136138, 371285004080958883, 371285004082742281, 371285004014807473, 371285004036775047, 371285004205160545, 371285004206942704, 371285003925707222, 371285003645048757]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483504606802679, 362483545626928202⟩, ⟨75954209576519929, 77427076458075019⟩, true⟩

def words04 : List Nat := [371285003363634027, 371285003263966639, 371285003034569575, 371285003053009388, 371285003054401947, 371285003016474866, 371285002506468918, 371285002350933346, 371285002390395382, 371285002392242560]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480370892427793, 362480411928837877⟩, ⟨242546894820198920, 244020627308257642⟩, true⟩

def words05 : List Nat := [371285002366190635, 371285002270407288, 371285002328691607, 371285002330674071, 371285002395681842, 371285002483883149, 371285002547349868, 371285002549163605, 371285002318218827, 371285002234091983]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475240037733493, 362475281090011253⟩, ⟨515359906931777689, 516834483029151983⟩, true⟩

def words06 : List Nat := [371285002415993912, 371285002417780667, 371285002319264161, 371285002155426477, 371285001990952371, 371285001848071077, 371285001528105106, 371285001530381082, 371285001531715199, 371285001505339994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503667161383200, 362503708229781129⟩, ⟨(-996180567950857643), (-994705134662212711)⟩, true⟩

def words07 : List Nat := [371285001494197027, 371285001666822190, 371285002191735841, 371285002400654779, 371285002555130661, 371285002710177302, 371285003132060127, 371285003378133468, 371285003731092181, 371285004084792088]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493217673138526, 362493258757641623⟩, ⟨(-440517267902734231), (-439040978059210049)⟩, true⟩

def words08 : List Nat := [371285004426408814, 371285004428192358, 371285004403450278, 371285004510295778, 371285004627528413, 371285004629344724, 371285004522512775, 371285004416227201, 371285004554081273, 371285004711316884]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478242825950348, 362478283926568177⟩, ⟨356129314863148856, 357606461926863622⟩, true⟩

def words09 : List Nat := [371285005159731160, 371285005608869093, 371285005941301695, 371285005943085640, 371285005804721301, 371285005775973868, 371285006068318287, 371285006070102780, 371285005976829109, 371285005852544246]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk531
