import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk383

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362517877087001494, 362517897828894358⟩, ⟨(-1259253048372198913), (-1258716201325580913)⟩, true⟩

def state01 : KState := ⟨⟨362505062731607079, 362505083484799682⟩, ⟨(-768443944308285759), (-767906664426506403)⟩, true⟩

def words00 : List Nat := [371285034811775087, 371285034981957227, 371285035833220265, 371285036685147644, 371285037677838802, 371285037855540953, 371285038046479071, 371285038237818397, 371285038934575205, 371285039459208429]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486701122649568, 362486721887139545⟩, ⟨(-64949898183352876), (-64412185442087384)⟩, true⟩

def words01 : List Nat := [371285040138730315, 371285040818717531, 371285041342121870, 371285041343374124, 371285040959434722, 371285040704878631, 371285040874761513, 371285040938371116, 371285040983173746, 371285041028460438]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362514184644951478, 362514205420644171⟩, ⟨(-1118191845311913932), (-1117653703224278974)⟩, true⟩

def words02 : List Nat := [371285041754166417, 371285042139271844, 371285043020902244, 371285043902997933, 371285044643175836, 371285044644428446, 371285044990876348, 371285045505541198, 371285046700244540, 371285047462249549]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502952633337806, 362502973420455863⟩, ⟨(-687530739448514441), (-686992159369339257)⟩, true⟩

def words03 : List Nat := [371285048227045310, 371285048992227721, 371285050437485748, 371285051543654339, 371285052481031229, 371285053418847405, 371285054343036958, 371285054532325000, 371285055000558108, 371285055469453820]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362506921957326102, 362506942755604216⟩, ⟨(-839722359716242902), (-839183351702310714)⟩, true⟩

def words04 : List Nat := [371285056426309579, 371285056683986546, 371285056939673877, 371285057195781533, 371285057657291127, 371285057950085928, 371285058808275874, 371285059666918198, 371285060528700509, 371285061100583427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362531005046569493, 362531025856201884⟩, ⟨(-1763412225882127098), (-1762872782375039850)⟩, true⟩

def words05 : List Nat := [371285062351937194, 371285063603894918, 371285065134466817, 371285065851973383, 371285066463299691, 371285067074973314, 371285068027524508, 371285068639632316, 371285069838533778, 371285071037965263]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480587750899121, 362480608571837509⟩, ⟨170814978111376239, 171354855374220587⟩, true⟩

def words06 : List Nat := [371285072226307244, 371285072509887044, 371285073193712301, 371285073878134612, 371285074767581198, 371285074768835125, 371285074753512729, 371285074561502538, 371285074425382710, 371285074426812079]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484405288509471, 362484426120727447⟩, ⟨24453919247756526, 24994229365331230⟩, true⟩

def words07 : List Nat := [371285074874123995, 371285075438291217, 371285076000315704, 371285076001591593, 371285076192067942, 371285076384888638, 371285077256062341, 371285077365924288, 371285077366868380, 371285077351299759]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501064611203267, 362501085454663797⟩, ⟨(-614993374863939937), (-614452633198786523)⟩, true⟩

def words08 : List Nat := [371285077597181638, 371285077598563286, 371285078067208744, 371285078612979737, 371285079042179295, 371285079043437296, 371285079008684694, 371285079236546928, 371285079914591067, 371285080332807144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497778049808421, 362497798904698406⟩, ⟨(-488734332567126690), (-488193152069692546)⟩, true⟩

def words09 : List Nat := [371285080710090401, 371285081087788313, 371285082143421910, 371285082884645605, 371285083664978757, 371285084445725941, 371285085224211842, 371285085225467169, 371285085539789175, 371285085872431807]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk383
