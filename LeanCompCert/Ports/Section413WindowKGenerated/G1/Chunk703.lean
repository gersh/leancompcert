import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469156423862617, 362469229792774813⟩, ⟨1127633272762264937, 1131116668662097981⟩, true⟩

def state01 : KState := ⟨⟨362474686938624011, 362474760329121650⟩, ⟨738794914256600497, 742279827718670429⟩, true⟩

def words00 : List Nat := [371285319418616129, 371285319216185325, 371285318911491738, 371285318786550541, 371285318660817426, 371285318510600504, 371285318090196339, 371285317851124754, 371285317610756022, 371285317573151215]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470559652954281, 362470633065400978⟩, ⟨1029035621966185479, 1032522078777146627⟩, true⟩

def words01 : List Nat := [371285317424803094, 371285317260563232, 371285317130291245, 371285317132944581, 371285317068443114, 371285316987720967, 371285316906235476, 371285316819887669, 371285316463439517, 371285316257647525]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468631253514706, 362468704687432028⟩, ⟨1164688858496284714, 1168176825234288104⟩, true⟩

def words02 : List Nat := [371285316050478412, 371285316045966538, 371285315872403052, 371285315659117619, 371285315444941233, 371285315250576590, 371285314954406420, 371285314861059966, 371285314766917514, 371285314623806752]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498504412161176, 362498577867821487⟩, ⟨(-936431207888937453), (-932941711855946473)⟩, true⟩

def words03 : List Nat := [371285314389272671, 371285314329411259, 371285314378425083, 371285314380853515, 371285314354473232, 371285314296656003, 371285314335045115, 371285314358024551, 371285314548222450, 371285314739463120]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478765381281130, 362478838858699685⟩, ⟨452036915601313682, 455527942219135076⟩, true⟩

def words04 : List Nat := [371285314930263583, 371285314932672462, 371285314854202867, 371285314825789728, 371285314796149145, 371285314774224572, 371285314544396621, 371285314310678854, 371285314076008354, 371285314024900384]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362466251841824245, 362466325340944355⟩, ⟨1332516003327296752, 1336008556759964572⟩, true⟩

def words05 : List Nat := [371285314044104693, 371285314156358758, 371285314267424526, 371285314269835883, 371285314161017978, 371285314114994332, 371285314067749702, 371285314051533375, 371285313791103577, 371285313523956862]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469945461315387, 362470018982008039⟩, ⟨1072662165005553960, 1076156236392994628⟩, true⟩

def words06 : List Nat := [371285313255723359, 371285313163452531, 371285312970408249, 371285312907142960, 371285312843104943, 371285312747234557, 371285312400121295, 371285312159242233, 371285311917093472, 371285311809013766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485229998062911, 362485303540731865⟩, ⟨(-3010525366802334), 485092600179938⟩, true⟩

def words07 : List Nat := [371285311593546750, 371285311342196199, 371285311089893548, 371285311040139196, 371285310896099004, 371285310807678234, 371285310718418948, 371285310630258034, 371285310430309417, 371285310433209845]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478049640517707, 362478123204631496⟩, ⟨502430579567175146, 505927706934457838⟩, true⟩

def words08 : List Nat := [371285310636122801, 371285310647187655, 371285310648991064, 371285310642556580, 371285310635195945, 371285310637156637, 371285310601091654, 371285310667676335, 371285310696196938, 371285310698692222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489092325634048, 362489165911611272⟩, ⟨(-274869010972946986), (-271370344532691958)⟩, true⟩

def words09 : List Nat := [371285310665680944, 371285310736096975, 371285311006607134, 371285311036833087, 371285311059024138, 371285311081930575, 371285311170759222, 371285311173440664, 371285311216451453, 371285311273970718]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703
