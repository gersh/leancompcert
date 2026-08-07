import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465932426412114, 362466015891082556⟩, ⟨1434365044184408619, 1438581140803562405⟩, true⟩

def state01 : KState := ⟨⟨362472682170104229, 362472765657821736⟩, ⟨929512915365290520, 933730736023901804⟩, true⟩

def words00 : List Nat := [371285248003906538, 371285247908559574, 371285247764413902, 371285247722813161, 371285247680435424, 371285247609569658, 371285247320767919, 371285247196391654, 371285247070662963, 371285247020420639]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467577477713566, 362467660988853330⟩, ⟨1311445634640966895, 1315665207634436023⟩, true⟩

def words01 : List Nat := [371285246855518947, 371285246655765218, 371285246454992265, 371285246414809379, 371285246289151377, 371285246198418620, 371285246106757951, 371285245985828650, 371285245626056799, 371285245394194609]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472482531263571, 362472566065362630⟩, ⟨944453442018644066, 948674732946396262⟩, true⟩

def words02 : List Nat := [371285245160920784, 371285245106933885, 371285244933745678, 371285244727938500, 371285244521129687, 371285244340993104, 371285244070845004, 371285243980144451, 371285243888586772, 371285243797995884]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490600209394481, 362490683766757709⟩, ⟨(-411365392376530916), (-407142360470808018)⟩, true⟩

def words03 : List Nat := [371285243639292277, 371285243651376556, 371285243754348641, 371285243756932784, 371285243718840238, 371285243654778698, 371285243597510902, 371285243600348361, 371285243593337916, 371285243668944067]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479612689990875, 362479696270606821⟩, ⟨410974500403543035, 415199272656014315⟩, true⟩

def words04 : List Nat := [371285243731554390, 371285243734133268, 371285243651510239, 371285243701644309, 371285243805116392, 371285243807691615, 371285243673442355, 371285243528079721, 371285243381638092, 371285243355077844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470391273697698, 362470474877491531⟩, ⟨1101239373968560531, 1105465881207304955⟩, true⟩

def words05 : List Nat := [371285243282752402, 371285243224049150, 371285243164519000, 371285243104933083, 371285242873815651, 371285242649653160, 371285242424138401, 371285242377760441, 371285242182237166, 371285241987846959]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489240977183594, 362489324604024771⟩, ⟨(-309908529493526673), (-305680296812205397)⟩, true⟩

def words06 : List Nat := [371285241792333263, 371285241776184835, 371285241710893555, 371285241754500148, 371285241757369324, 371285241759964105, 371285241633962355, 371285241627096243, 371285241787189296, 371285241844387366]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484256071644145, 362484339722045824⟩, ⟨63383956210574859, 67613952976359933⟩, true⟩

def words07 : List Nat := [371285241880339707, 371285241917213390, 371285242131156457, 371285242257048162, 371285242431578806, 371285242607066380, 371285242746180738, 371285242748759370, 371285242694943430, 371285242686161428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478113433727355, 362478197107058226⟩, ⟨523389385378844235, 527621099202082553⟩, true⟩

def words08 : List Nat := [371285242821243286, 371285242823819744, 371285242733512383, 371285242636337153, 371285242538205464, 371285242455029324, 371285242333604001, 371285242363932974, 371285242385459043, 371285242388126488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490122920707945, 362490206617339882⟩, ⟨(-376060764866886655), (-371827305911435463)⟩, true⟩

def words09 : List Nat := [371285242379857346, 371285242466968175, 371285242594969565, 371285242597546468, 371285242488191647, 371285242350841153, 371285242250341826, 371285242253217334, 371285242297914735, 371285242367117436]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748
