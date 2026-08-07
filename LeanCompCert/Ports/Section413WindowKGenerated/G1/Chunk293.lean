import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk293

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504279889816917, 362504291761693913⟩, ⟨(-551310877138875820), (-551075747582973694)⟩, true⟩

def state01 : KState := ⟨⟨362489086047779187, 362489097928126133⟩, ⟨(-105993133293412074), (-105757755525443632)⟩, true⟩

def words00 : List Nat := [371285485002929061, 371285485075977640, 371285486312597559, 371285487549643696, 371285489139645438, 371285489179439057, 371285489222049403, 371285489264966423, 371285489678830928, 371285489803001592]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362454253604421250, 362454265493218050⟩, ⟨915294536793151503, 915530162269510737⟩, true⟩

def words01 : List Nat := [371285491089931203, 371285492377166340, 371285493651087405, 371285493652025069, 371285493376227842, 371285492957489848, 371285492964065610, 371285492965003617, 371285492006099022, 371285490942135837]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492867506795040, 362492879404007867⟩, ⟨(-217065947113741456), (-216830074837851324)⟩, true⟩

def words02 : List Nat := [371285489877821313, 371285489849516696, 371285489257586036, 371285488950958833, 371285488644073718, 371285487955083413, 371285486492606434, 371285486192610334, 371285486628562712, 371285486881596840]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497071320522510, 362497083226269128⟩, ⟨(-340312444434426430), (-340076321818372622)⟩, true⟩

def words03 : List Nat := [371285487122331343, 371285487363350143, 371285488765346689, 371285489586538039, 371285490760969954, 371285491935690451, 371285492717612306, 371285492718550958, 371285492348427038, 371285492744628476]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485595748986466, 362485607663101008⟩, ⟨(-3559038474610960), (-3322670301162694)⟩, true⟩

def words04 : List Nat := [371285493613616381, 371285493614557644, 371285493298243576, 371285492985099532, 371285492711229407, 371285492712263819, 371285492998496174, 371285493722401371, 371285494453600012, 371285494458429918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362515193926329384, 362515205848956492⟩, ⟨(-872380076544395885), (-872143458484270739)⟩, true⟩

def words05 : List Nat := [371285494911388433, 371285495364797771, 371285496843042814, 371285497220265311, 371285497464937640, 371285497709875270, 371285498909843006, 371285499676787321, 371285500689221992, 371285501702010398]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489358505050577, 362489370436140106⟩, ⟨(-113816392944127279), (-113579526382682355)⟩, true⟩

def words06 : List Nat := [371285502717656292, 371285502718595981, 371285503232324308, 371285504069421176, 371285504954507328, 371285504955446937, 371285504296452607, 371285503621889358, 371285503239747476, 371285503372492880]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466024880970440, 362466036820534121⟩, ⟨571764841170716297, 572001956659766571⟩, true⟩

def words07 : List Nat := [371285504320731418, 371285505269294380, 371285506221050129, 371285506221992182, 371285506035941666, 371285506088639536, 371285506991107833, 371285506992048473, 371285506575317119, 371285505913681152]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362515438575284381, 362515450523252365⟩, ⟨(-880232436284218367), (-879995073832857357)⟩, true⟩

def words08 : List Nat := [371285505251681855, 371285505174827826, 371285505154290835, 371285505723342705, 371285506128021205, 371285506128977929, 371285506173291176, 371285506774756670, 371285508532696339, 371285509552416638]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493006278967322, 362493018235534683⟩, ⟨(-220859411473562690), (-220621796244785554)⟩, true⟩

def words09 : List Nat := [371285510407573896, 371285511263008415, 371285512143686297, 371285512559382126, 371285513327309391, 371285514095535108, 371285514735855575, 371285514736796569, 371285514091611075, 371285514348039538]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk293
