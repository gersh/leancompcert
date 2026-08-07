import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk177

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362445935380808647, 362445939530388009⟩, ⟨703886924933336435, 703936604616799625⟩, true⟩

def state01 : KState := ⟨⟨362457327497692804, 362457331652123062⟩, ⟨502124116235015405, 502173881804492251⟩, true⟩

def words00 : List Nat := [371285708036530839, 371285708037074997, 371285704721905968, 371285700813727190, 371285696905777888, 371285693958942398, 371285689838971426, 371285688903069154, 371285687967093232, 371285687037882774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362514590939294356, 362514595098646588⟩, ⟨(-512093079612543505), (-512043226850264441)⟩, true⟩

def words01 : List Nat := [371285686655442919, 371285687874163894, 371285692273573218, 371285693443323305, 371285694107433218, 371285694771632667, 371285696744968921, 371285697122216642, 371285698753400240, 371285700384643413]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454656219287614, 362454660383557272⟩, ⟨549994633050372753, 550044572974879219⟩, true⟩

def words02 : List Nat := [371285701422539313, 371285701423084232, 371285698224848852, 371285697485454149, 371285696962518499, 371285696963063565, 371285692946268786, 371285688827224322, 371285684708416336, 371285683766127768]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362410519769865858, 362410523939043444⟩, ⟨1332716222348074615, 1332766249315483505⟩, true⟩

def words03 : List Nat := [371285682016836372, 371285680660231931, 371285679303595516, 371285677661639163, 371285671788921686, 371285666872021000, 371285661955389338, 371285660212803091, 371285655921598991, 371285651687031916]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474783036368566, 362474787210426728⟩, ⟨192421735732484271, 192471849306004829⟩, true⟩

def words04 : List Nat := [371285647452706048, 371285646026210511, 371285643008909211, 371285641632296209, 371285640255671341, 371285638391068032, 371285633296587043, 371285631372777534, 371285630694329452, 371285630694894672]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362460006948284419, 362460011127325085⟩, ⟨454915529732110815, 454965731769823745⟩, true⟩

def words05 : List Nat := [371285630084436637, 371285629024223439, 371285629267748959, 371285629512062170, 371285630397599219, 371285631283240537, 371285632140491667, 371285632141040193, 371285630008998812, 371285628567176990]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362440660285568362, 362440664469470067⟩, ⟨798741210323114984, 798791498718257216⟩, true⟩

def words06 : List Nat := [371285628849117853, 371285628849664021, 371285626919175812, 371285625067759257, 371285623216352267, 371285620952186637, 371285617724242454, 371285617201834377, 371285616679296703, 371285616157636542]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470353136427700, 362470357325267215⟩, ⟨270911348003156586, 270961724168571462⟩, true⟩

def words07 : List Nat := [371285613628512660, 371285613145809320, 371285613479245655, 371285613479792151, 371285610084914128, 371285606272852422, 371285602460987775, 371285600959147415, 371285597873845467, 371285597017290195]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362434587592423529, 362434591786191785⟩, ⟨906901914766346442, 906952378589870744⟩, true⟩

def words08 : List Nat := [371285596160621611, 371285595306229557, 371285591247467329, 371285590346475701, 371285589493517707, 371285589494064574, 371285585337400576, 371285580108847875, 371285574880666507, 371285572808034949]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362441778745050720, 362441782943748018⟩, ⟨779253123102009462, 779303674638398448⟩, true⟩

def words09 : List Nat := [371285570231835098, 371285570521383104, 371285570852090014, 371285570852647143, 371285569166188650, 371285568431217340, 371285568511332067, 371285568511883013, 371285566508196126, 371285564049064782]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk177
