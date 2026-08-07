import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498273862165988, 362498335011701591⟩, ⟨(-827935205908632769), (-825275351825568761)⟩, true⟩

def state01 : KState := ⟨⟨362485084367372803, 362485145536649476⟩, ⟨21511779390918301, 24172904901188371⟩, true⟩

def words00 : List Nat := [371285520575932162, 371285520578133142, 371285520757133108, 371285520969098788, 371285521190705858, 371285521192896468, 371285521093352156, 371285520948000385, 371285520831535529, 371285520834039652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482070174664561, 362482131363652398⟩, ⟨215727650276768570, 218390045482613692⟩, true⟩

def words01 : List Nat := [371285521006976121, 371285521186604179, 371285521333537925, 371285521335768185, 371285521334319148, 371285521357817969, 371285521568421004, 371285521570613948, 371285521510786851, 371285521460601834]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480614464197688, 362480675672832299⟩, ⟨309532079054975088, 312195740006100626⟩, true⟩

def words02 : List Nat := [371285521456499820, 371285521458939303, 371285521488623852, 371285521592229508, 371285521655930888, 371285521658122338, 371285521400570850, 371285521267628931, 371285521173273711, 371285521175548520]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493352325391524, 362493413554011005⟩, ⟨(-511239085529387727), (-508574136851794753)⟩, true⟩

def words03 : List Nat := [371285521101997966, 371285521029637452, 371285521122527940, 371285521171128151, 371285521226591695, 371285521282845775, 371285521331574748, 371285521333783725, 371285521339319337, 371285521464551627]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483774616052469, 362483835864230937⟩, ⟨106051273194862301, 108717482354133537⟩, true⟩

def words04 : List Nat := [371285521746713432, 371285521829714624, 371285521911361928, 371285521993726828, 371285522148305054, 371285522204242169, 371285522393948676, 371285522584574070, 371285522711956656, 371285522714228674]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362519601874070907, 362519663142040761⟩, ⟨(-2203172305247176701), (-2200504820432343935)⟩, true⟩

def words05 : List Nat := [371285522904170875, 371285523121392250, 371285523578285403, 371285523853738757, 371285524091738602, 371285524330474922, 371285524767013050, 371285525084130568, 371285525615218986, 371285526147262022]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498428433627795, 362498489721400941⟩, ⟨(-838278756768691917), (-835609995333980669)⟩, true⟩

def words06 : List Nat := [371285526677746618, 371285526915252115, 371285527251656960, 371285527589198689, 371285527998641504, 371285528088090243, 371285528166020020, 371285528244639851, 371285528496654453, 371285528700238962]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475797763195757, 362475859070727541⟩, ⟨620891596456897469, 623561631830237643⟩, true⟩

def words07 : List Nat := [371285529026203134, 371285529353058852, 371285529678439715, 371285529683822420, 371285529760548461, 371285529838357611, 371285529984504658, 371285529986698403, 371285529839039897, 371285529691568581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495441457004875, 362495502784158522⟩, ⟨(-645801436495132249), (-643130135801518541)⟩, true⟩

def words08 : List Nat := [371285529545309348, 371285529547742858, 371285529626375065, 371285529787604472, 371285529906386283, 371285529908584876, 371285529846567913, 371285529916573889, 371285530225897515, 371285530382803271]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496860760250367, 362496922107402526⟩, ⟨(-737390942438856678), (-734718351941622102)⟩, true⟩

def words09 : List Nat := [371285530482438570, 371285530582765249, 371285530719503286, 371285530736989593, 371285530826527886, 371285530916934472, 371285531005957679, 371285531008196242, 371285531122504905, 371285531301803518]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644
