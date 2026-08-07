import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk047

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360717627223111775, 360717627334187518⟩, ⟨(-637110806421116577), (-637110451935211289)⟩, true⟩

def state01 : KState := ⟨⟨360643982787558753, 360643982899136799⟩, ⟨(-292157497165703905), (-292157140316424871)⟩, true⟩

def words00 : List Nat := [360582106694614427, 360582106694667149, 360582074485445101, 360582080745668497, 360582080745712749, 360582074894638358, 360582058775433756, 360582019486057279, 360581980213357616, 360581966949165153]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360129833899206583, 360129834011283553⟩, ⟨2132024737985982634, 2132025097187692216⟩, true⟩

def words01 : List Nat := [360581978468782371, 360581989983520548, 360581989983567705, 360581978764786495, 360581923340075515, 360581837123187314, 360581750942839268, 360581688648496230, 360581629963165199, 360581534243738573]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360864484799412454, 360864484911989316⟩, ⟨(-1339383459993224985), (-1339383098429533569)⟩, true⟩

def words02 : List Nat := [360581438564850722, 360581387255495914, 360581374803209891, 360581390731583211, 360581390731633354, 360581364297507199, 360581327207974155, 360581309144038739, 360581317237847583, 360581377091564558]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360814968650843548, 360814968763926506⟩, ⟨(-1104475938457362386), (-1104475574497297398)⟩, true⟩

def words03 : List Nat := [360581409169248663, 360581441233384658, 360581517440281686, 360581617027450878, 360581704619578733, 360581792174733112, 360581857168921185, 360581907870279905, 360581957039288650, 360582006187571877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609277535345120, 360609277648929606⟩, ⟨(-129735697888240390), (-129735331548413156)⟩, true⟩

def words04 : List Nat := [360582060275106467, 360582070715871567, 360582070715919582, 360582049154401933, 360582027601964025, 360581979134248382, 360581971859599840, 360581979549142030, 360581979549189572, 360581970696383108]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360851951319392771, 360851951433481881⟩, ⟨(-1284576453675114432), (-1284576084935861170)⟩, true⟩

def words05 : List Nat := [360582020203128056, 360582069689057478, 360582111179365296, 360582111179418621, 360582109186711824, 360582069515507341, 360582029860971866, 360582025800909958, 360582082508018955, 360582139191319340]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360362250731559117, 360362250846157336⟩, ⟨1047079924101531545, 1047080295266680129⟩, true⟩

def words06 : List Nat := [360582168034225771, 360582168034279199, 360582153482953937, 360582144043406630, 360582134607807453, 360582113375599423, 360582048806018999, 360581948651502595, 360581848538978530, 360581764534892490]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360058450837766701, 360058450952869911⟩, ⟨2498757854594668214, 2498758228171171632⟩, true⟩

def words07 : List Nat := [360581718524940601, 360581683487261113, 360581648464257548, 360581582199385870, 360581542506628748, 360581489509476467, 360581436534497363, 360581396408689139, 360581313105601906, 360581203720269738]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360420874026230875, 360420874141842327⟩, ⟨763956033857002103, 763956409865418375⟩, true⟩

def words08 : List Nat := [360581094380684768, 360580983588615060, 360580895401357858, 360580850383603199, 360580805384660631, 360580717018462385, 360580585630199781, 360580497365554363, 360580409137753323, 360580363997764127]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360373352108956342, 360373352225080739⟩, ⟨992059876628534155, 992060255096573507⟩, true⟩

def words09 : List Nat := [360580330708341077, 360580275502699462, 360580220320083672, 360580227846869954, 360580227846915891, 360580215758794958, 360580203675708392, 360580160522415614, 360580074511974314, 360580031444892526]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk047
