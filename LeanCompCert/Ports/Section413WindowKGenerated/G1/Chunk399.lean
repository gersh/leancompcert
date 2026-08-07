import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk399

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496012703857713, 362496035290169023⟩, ⟨(-431300025342099417), (-430691050548435011)⟩, true⟩

def state01 : KState := ⟨⟨362479344490094719, 362479367088052500⟩, ⟨233904711074405470, 234514150622182566⟩, true⟩

def words00 : List Nat := [371285242197927691, 371285242357025863, 371285242497686663, 371285242638801449, 371285242838265405, 371285242839720815, 371285242880880102, 371285243031899471, 371285243161626297, 371285243162986657]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515680030616122, 362515702640401644⟩, ⟨(-1216355565933313632), (-1215745654279208562)⟩, true⟩

def words01 : List Nat := [371285243424302220, 371285243833514965, 371285244787356131, 371285245220715461, 371285245555800865, 371285245891259105, 371285246764580157, 371285247324652370, 371285248088456905, 371285248852814179]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484068378555688, 362484091000159720⟩, ⟨45592675645958580, 46203059155577496⟩, true⟩

def words02 : List Nat := [371285249493970792, 371285249495279348, 371285249380733986, 371285249462398932, 371285249732582872, 371285249733891512, 371285249168597325, 371285248604100848, 371285248100064130, 371285248101566071]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471908067322838, 362471930700688690⟩, ⟨531290855952985693, 531901709171491441⟩, true⟩

def words03 : List Nat := [371285248592786797, 371285249113479103, 371285249515291743, 371285249516601087, 371285249197284528, 371285248884444416, 371285248883186783, 371285248884498432, 371285248551685421, 371285248219696489]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475336103782112, 362475358748873936⟩, ⟨394441756557840041, 395053078171972329⟩, true⟩

def words04 : List Nat := [371285247887160994, 371285247876528929, 371285247921203830, 371285248203448749, 371285248381110650, 371285248382419719, 371285247725299022, 371285247577741722, 371285247435327314, 371285247436688003]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478160740942435, 362478183397984339⟩, ⟨281633038393074301, 282244837471839943⟩, true⟩

def words05 : List Nat := [371285247190156946, 371285246907566070, 371285246966552347, 371285246996869330, 371285247153815664, 371285247311267308, 371285247450735034, 371285247452044462, 371285246757215939, 371285246582105256]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474504113280225, 362474526782001781⟩, ⟨427822959626360424, 428435225484848730⟩, true⟩

def words06 : List Nat := [371285246779961177, 371285246781278435, 371285246722130914, 371285246450541284, 371285246178476034, 371285246097236207, 371285245702386080, 371285245702578571, 371285245702320110, 371285245701828773]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523284604149888, 362523307284689239⟩, ⟨(-1522135028201853564), (-1521522289924900630)⟩, true⟩

def words07 : List Nat := [371285245791884150, 371285246150752453, 371285247037406286, 371285247515774172, 371285247896456390, 371285248277535375, 371285248916415576, 371285249244623027, 371285250197439162, 371285251150777509]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501983398121818, 362502006090486151⟩, ⟨(-670495815725386557), (-669882604627281369)⟩, true⟩

def words08 : List Nat := [371285252103955741, 371285252224323692, 371285252969318906, 371285253715004353, 371285254483785718, 371285254485096170, 371285254420938706, 371285254351657030, 371285254836061367, 371285255256432807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469535160683482, 362469557864878849⟩, ⟨627306879738552528, 627920564019078908⟩, true⟩

def words09 : List Nat := [371285255831033923, 371285256406134285, 371285256981110161, 371285256982421056, 371285256724658030, 371285256606358768, 371285256636831028, 371285256638164723, 371285256269946227, 371285255878979326]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk399
