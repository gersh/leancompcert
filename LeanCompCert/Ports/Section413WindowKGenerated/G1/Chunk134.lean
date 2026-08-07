import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk134

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362569468116315059, 362569470436623784⟩, ⟨(-1136332346604405925), (-1136311309956361535)⟩, true⟩

def state01 : KState := ⟨⟨362417006041452143, 362417008365383491⟩, ⟨907346225441341437, 907367310651459017⟩, true⟩

def words00 : List Nat := [371284683695017522, 371284683695419113, 371284685091512607, 371284687613068596, 371284690354809712, 371284690355211446, 371284685694644303, 371284680584293535, 371284675474539280, 371284671848653548]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362387092291051306, 362387094618603324⟩, ⟨1309054290426477760, 1309075424208208808⟩, true⟩

def words01 : List Nat := [371284667309641680, 371284667816092590, 371284667816394176, 371284667579381485, 371284661694988601, 371284657467607863, 371284654561027374, 371284654561429427, 371284648491333352, 371284641222493653]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484906224850399, 362484908556000522⟩, ⟨(-3868465118592948), (-3847283031668056)⟩, true⟩

def words02 : List Nat := [371284633954560133, 371284632231838254, 371284627811578822, 371284627873880905, 371284627874192642, 371284627056863721, 371284621829145013, 371284620701174603, 371284622086258340, 371284622108004717]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362427225265141353, 362427227599965561⟩, ⟨771044523239188140, 771065754687050560⟩, true⟩

def words03 : List Nat := [371284622108307992, 371284620687051487, 371284619265844882, 371284618951385308, 371284615881404034, 371284614472082373, 371284613062841597, 371284611631337844, 371284602832334539, 371284598563855967]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362417493610913358, 362417495949323192⟩, ⟨902303389262719187, 902324668920189815⟩, true⟩

def words04 : List Nat := [371284595553026054, 371284595553433432, 371284593911134888, 371284592263981417, 371284590632864156, 371284590633312089, 371284588077104017, 371284586480570769, 371284584884135954, 371284583285302389]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362560245595211546, 362560247937258858⟩, ⟨(-1018383066535321242), (-1018361737935288820)⟩, true⟩

def words05 : List Nat := [371284578827128938, 371284579356616125, 371284582682372114, 371284582682782296, 371284582059275352, 371284580460438662, 371284582773900253, 371284583939364396, 371284589561035023, 371284595182044886]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362509393797595448, 362509396143287134⟩, ⟨(-333919715568817046), (-333898337897383640)⟩, true⟩

def words06 : List Nat := [371284599696076506, 371284599696479884, 371284601785385978, 371284605583570002, 371284611043409622, 371284611043812981, 371284609166188961, 371284606892394049, 371284607847512301, 371284609688094693]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362452150830714117, 362452153180038717⟩, ⟨437630762863425315, 437652189489190205⟩, true⟩

def words07 : List Nat := [371284615524175485, 371284621359558319, 371284627205072791, 371284627205476458, 371284625722118646, 371284623573475063, 371284624771398425, 371284624771802765, 371284622367911261, 371284619959674414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490265604716875, 362490267957664164⟩, ⟨(-76172516833545777), (-76151041355554675)⟩, true⟩

def words08 : List Nat := [371284617551614733, 371284617013999183, 371284616509847125, 371284618459458302, 371284619760681720, 371284619761088439, 371284618135003611, 371284620066007256, 371284622957885859, 371284623376732021]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362533054540365661, 362533056896995239⟩, ⟨(-653556526314465907), (-653535001143870971)⟩, true⟩

def words09 : List Nat := [371284623779412727, 371284624182163263, 371284629169472622, 371284632202323637, 371284636900783491, 371284641598712329, 371284645201597306, 371284645202002931, 371284646896409584, 371284650482570836]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk134
