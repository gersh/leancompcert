import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk025

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360041898164349376, 360041898193591126⟩, ⟨1299535735044982619, 1299535784757592891⟩, true⟩

def state01 : KState := ⟨⟨360836904891225252, 360836904920715692⟩, ⟨(-691222322324252938), (-691222271988670774)⟩, true⟩

def words00 : List Nat := [360561504664926998, 360561357062224692, 360561385624514721, 360561478269088378, 360561478269112637, 360561433139438408, 360561428793323580, 360561455530210060, 360561517561330372, 360561627233742904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360135908861482324, 360135908891225146⟩, ⟨1072499031430712468, 1072499082401032110⟩, true⟩

def words01 : List Nat := [360561649343725756, 360561671436114771, 360561683239246256, 360561778038505550, 360561830266023521, 360561882452046037, 360561882452069645, 360561854015788686, 360561672719062971, 360561503765193810]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360295132591346419, 360295132621339078⟩, ⟨670599286749299635, 670599338350477801⟩, true⟩

def words02 : List Nat := [360561334945352618, 360561320400016790, 360561286289924344, 360561156430572345, 360561026674075001, 360560839849788861, 360560734665882577, 360560579970597561, 360560425397646976, 360560191648355078]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361225032612631439, 361225032642874958⟩, ⟨(-1687465197544864559), (-1687465145307743641)⟩, true⟩

def words03 : List Nat := [360560135329995127, 360560183698442539, 360560266365578246, 360560360612949785, 360560360612974360, 360560321708912379, 360560304855038513, 360560414625768800, 360560676286427057, 360560937741140309]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361495922429266565, 361495922459764299⟩, ⟨(-2380851378838711041), (-2380851325954638755)⟩, true⟩

def words04 : List Nat := [360561054803183173, 360561127490451478, 360561351740971024, 360561575815269915, 360561758272823167, 360561902739520172, 360561969994131168, 360562037195976055, 360562255273085054, 360562621273580592]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360728654082993395, 360728654113743033⟩, ⟨(-418729972161218003), (-418729918633482521)⟩, true⟩

def words05 : List Nat := [360563137799119741, 360563653920022122, 360564055560423885, 360564308929943412, 360564449582941964, 360564590125933303, 360564880953731516, 360565023821142169, 360565087739249097, 360565151607443353]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653414659324084, 360653414690327919⟩, ⟨(-224626803269256795), (-224626749089504767)⟩, true⟩

def words06 : List Nat := [360565251606023930, 360565475286089444, 360565712233074113, 360565948995309773, 360566060059620933, 360566060059647855, 360566023833950257, 360566022840616260, 360566021848048264, 360566045281891706]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624630780876029, 360624630812136784⟩, ⟨(-150622816198759928), (-150622761357429516)⟩, true⟩

def words07 : List Nat := [360566045281915709, 360566001822478079, 360565984211800341, 360566134544089660, 360566232608887338, 360566330597582134, 360566351875155175, 360566351875182213, 360566249896851319, 360566272516376448]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360196099538648870, 360196099570165131⟩, ⟨954765111645946670, 954765167147773776⟩, true⟩

def words08 : List Nat := [360566352843883281, 360566352843910350, 360566287452047348, 360566092983095181, 360565898664598235, 360565596051151451, 360565371261296771, 360565184069029787, 360564997021365697, 360564734769836087]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360519321535285247, 360519321567058281⟩, ⟨116864163761881535, 116864219930075475⟩, true⟩

def words09 : List Nat := [360564596024085094, 360564599550880233, 360564748659964780, 360564753120491548, 360564753120516583, 360564630495989551, 360564507965893100, 360564359002090828, 360564286638184257, 360564269343954464]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk025
