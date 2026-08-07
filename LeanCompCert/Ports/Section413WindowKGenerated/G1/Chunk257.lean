import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk257

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498606836235824, 362498615870083372⟩, ⟨(-335123273989618943), (-334966311142138027)⟩, true⟩

def state01 : KState := ⟨⟨362457584878975986, 362457593920161287⟩, ⟨719285252470219011, 719442403934333085⟩, true⟩

def words00 : List Nat := [371285583191131903, 371285583191944946, 371285582199120001, 371285582459960217, 371285582965373863, 371285582966186894, 371285581456028745, 371285579525898733, 371285577595597148, 371285576899699768]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471269040214186, 362471278088738498⟩, ⟨367421048463766388, 367578388652005862⟩, true⟩

def words01 : List Nat := [371285575811895884, 371285575349009553, 371285574885881160, 371285574440376441, 371285572951925941, 371285571707053035, 371285570727380422, 371285570728213600, 371285570182714887, 371285569627955139]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477893264243901, 362477902320053670⟩, ⟨197105358709766093, 197262886316414075⟩, true⟩

def words02 : List Nat := [371285569351790821, 371285569352695308, 371285569505104134, 371285570138579731, 371285570397803961, 371285570398619545, 371285569110690096, 371285568808052545, 371285568968503937, 371285568969346963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481772522759939, 362481781585995972⟩, ⟨97388929910458060, 97546648631780212⟩, true⟩

def words03 : List Nat := [371285568672008612, 371285568348753805, 371285569210018898, 371285569646431148, 371285570540065483, 371285571433947988, 371285572193705440, 371285572194521909, 371285571423301929, 371285571277085008]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485765794174743, 362485774864657744⟩, ⟨(-5347313187437268), (-5189407890880800)⟩, true⟩

def words04 : List Nat := [371285572491324600, 371285572492139151, 371285572096719473, 371285571692074674, 371285571287141593, 371285571225706913, 371285571517065613, 371285572417081881, 371285573333410150, 371285573342080335]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362509873337304941, 362509882415175780⟩, ⟨(-626347796649386442), (-626189701080420430)⟩, true⟩

def words05 : List Nat := [371285574117202444, 371285574892689243, 371285576048981105, 371285576049796007, 371285575443581521, 371285574370007299, 371285573425180669, 371285573426087689, 371285573807823994, 371285574752387829]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362505358603273649, 362505367688490142⟩, ⟨(-510080844611734469), (-509922559780328473)⟩, true⟩

def words06 : List Nat := [371285575721998951, 371285575722819470, 371285576487726958, 371285577623780842, 371285579215836715, 371285579384810103, 371285579385436515, 371285579233837031, 371285580238597775, 371285581007345432]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498015547065792, 362498024639619303⟩, ⟨(-320619194017216638), (-320460720073174086)⟩, true⟩

def words07 : List Nat := [371285583280618408, 371285585554040262, 371285587510488806, 371285588248588811, 371285589438425191, 371285590628589836, 371285593097130065, 371285593561637994, 371285594044449726, 371285594527518408]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464563979958771, 362464573079821475⟩, ⟨541993812584313264, 542152474996872198⟩, true⟩

def words08 : List Nat := [371285595305881109, 371285595338412176, 371285595936870724, 371285596535624285, 371285596935323880, 371285596936139755, 371285595332676571, 371285595041545095, 371285594888786910, 371285594889631358]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464403716629840, 362464412823932032⟩, ⟨546185012042985753, 546343866356950455⟩, true⟩

def words09 : List Nat := [371285594075158921, 371285593251308209, 371285593105098733, 371285593106005896, 371285593028997224, 371285592717407174, 371285592405574396, 371285592084737878, 371285589762576403, 371285588942783077]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk257
