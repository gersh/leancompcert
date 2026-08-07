import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk061

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360197559864149565, 360197560056565327⟩, ⟨2267715562527576793, 2267716358923118497⟩, true⟩

def state01 : KState := ⟨⟨360512202911865336, 360512203104943782⟩, ⟨346892557801124280, 346893358242307458⟩, true⟩

def words00 : List Nat := [360569255903028224, 360569221644131289, 360569200966753044, 360569187980470090, 360569174998435271, 360569133642236414, 360569080681620903, 360569042189399574, 360569003709759941, 360568977795327139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360656788059493131, 360656788253242762⟩, ⟨(-537797935096087272), (-537797130550644758)⟩, true⟩

def words01 : List Nat := [360568968504818596, 360568936479054988, 360568904463756051, 360568907109666064, 360568908120917017, 360568909131849158, 360568909131911875, 360568898543911972, 360568912905032723, 360568927261484774]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360493056472681964, 360493056667094665⟩, ⟨465019583812480657, 465020392419324665⟩, true⟩

def words02 : List Nat := [360568968059407792, 360568982527020968, 360568982527084036, 360568979179197073, 360568975832392969, 360568954329791570, 360568946348217452, 360568941278532775, 360568936210495375, 360568916437473022]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360621418331097658, 360621418526177488⟩, ⟨(-321988218571542027), (-321987405871900669)⟩, true⟩

def words03 : List Nat := [360568918062017795, 360568932055167421, 360568972401956993, 360568986531536150, 360568986531601146, 360568978038045208, 360568969547243865, 360568969038202698, 360568977580522764, 360568986120075567]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360563417332417306, 360563417528169851⟩, ⟨33820984097408055, 33821800930868713⟩, true⟩

def words04 : List Nat := [360568986120138609, 360568977115094955, 360568962662299528, 360568968579888097, 360568968579947372, 360568967801949005, 360568967802012580, 360568954987158648, 360568942176460074, 360568917007996009]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360363011901346616, 360363012097767102⟩, ⟨1268301355446086931, 1268302176390746377⟩, true⟩

def words05 : List Nat := [360568941445548700, 360568966768959838, 360568972045919100, 360568972045990097, 360568970272473480, 360568961505978375, 360568958725872133, 360568958725943001, 360568938737794586, 360568905308220146]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360541693904095653, 360541694101184942⟩, ⟨167315893995485711, 167316719063367017⟩, true⟩

def words06 : List Nat := [360568871889480343, 360568852581382006, 360568874968728811, 360568899208547717, 360568900308107855, 360568900308178808, 360568875476075955, 360568849461681030, 360568823455699671, 360568811883853235]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360381565084746646, 360381565282512269⟩, ⟨1156359489348974313, 1156360318593131681⟩, true⟩

def words07 : List Nat := [360568807489526755, 360568779514583885, 360568751548691272, 360568767831249266, 360568768320307250, 360568768809217931, 360568768809281309, 360568751761015530, 360568708884728537, 360568678602672970]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360333549741781873, 360333549940218279⟩, ⟨1452978920317923191, 1452979753710956105⟩, true⟩

def words08 : List Nat := [360568648330393750, 360568616943759274, 360568582702245271, 360568534237853361, 360568485789121585, 360568430529370891, 360568388485287098, 360568356774376661, 360568325073704371, 360568280110446221]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618576200059306, 360618576399168285⟩, ⟨(-313665742955880036), (-313664905396237014)⟩, true⟩

def words09 : List Nat := [360568242195761605, 360568216881818348, 360568191576029318, 360568169223156051, 360568138406562250, 360568081906266826, 360568025424192692, 360567994732189720, 360567985285320786, 360567993443935865]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk061
