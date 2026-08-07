import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607984691492624, 360608001573111622⟩, ⟨(-1349968478258348386), (-1349377613099077978)⟩, true⟩

def state01 : KState := ⟨⟨360593039528139638, 360593056416581382⟩, ⟨(-575885952967514826), (-575294734355915146)⟩, true⟩

def words00 : List Nat := [360581952602156761, 360581952649483612, 360581953068626255, 360581953487970283, 360581953698923052, 360581953699640057, 360581953538896869, 360581953093104448, 360581952647191991, 360581952698560964]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589509115417951, 360589526010608292⟩, ⟨(-392893551227901230), (-392301982937122830)⟩, true⟩

def words01 : List Nat := [360581953215480831, 360581953732518119, 360581954003623311, 360581954285080410, 360581954401110582, 360581954517328190, 360581955005101079, 360581955388740599, 360581955535475000, 360581955682306308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611425431845800, 360611442333811897⟩, ⟨(-1528836910040710923), (-1528244990596422657)⟩, true⟩

def words02 : List Nat := [360581955682900224, 360581955778504083, 360581956120670055, 360581956462960102, 360581956492303265, 360581956493020606, 360581956179807584, 360581956209546035, 360581956610696136, 360581957180320813]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591849943235270, 360591866852037711⟩, ⟨(-514161554432137210), (-513569280625987260)⟩, true⟩

def words03 : List Nat := [360581957511683192, 360581957843109032, 360581958299729645, 360581958983089529, 360581959407925711, 360581959832852220, 360581960024393981, 360581960025111501, 360581960036384296, 360581960228310816]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614230497283238, 360614247412852852⟩, ⟨(-1674485474981560386), (-1673892850331568832)⟩, true⟩

def words04 : List Nat := [360581960673350396, 360581961231656643, 360581961507690234, 360581961783790656, 360581961967032779, 360581962338544831, 360581963002652651, 360581963666872303, 360581964039873124, 360581964663237000]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360660557747669566, 360660574670011477⟩, ⟨(-4076843271092715517), (-4076250295265220975)⟩, true⟩

def words05 : List Nat := [360581965449974129, 360581966236890866, 360581967394851024, 360581968498215320, 360581969282656869, 360581970067136546, 360581970960759317, 360581972106061401, 360581973622310111, 360581975138662965]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609060088161936, 360609077017351919⟩, ⟨(-1406143810971979047), (-1405550479971382715)⟩, true⟩

def words06 : List Nat := [360581976432788418, 360581977355995316, 360581978177064123, 360581978998301284, 360581979465898584, 360581979562671504, 360581979563319419, 360581979404024011, 360581979455688841, 360581979978930231]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572202821128423, 360572219757072432⟩, ⟨505970875669920340, 506564557036542338⟩, true⟩

def words07 : List Nat := [360581980872971794, 360581981767116467, 360581982474717071, 360581982974434278, 360581983354291075, 360581983734335406, 360581984103827048, 360581984104545182, 360581984103310289, 360581983915843376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571957367071629, 360571974309793131⟩, ⟨518752528788409484, 519346561805184042⟩, true⟩

def words08 : List Nat := [360581983741842056, 360581983944010448, 360581984234206317, 360581984524540238, 360581984525208542, 360581984500593550, 360581984105191814, 360581983654250368, 360581983203115546, 360581982915725010]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598241187801568, 360598258137372299⟩, ⟨(-845347965012324023), (-844753576555771549)⟩, true⟩

def words09 : List Nat := [360581982723498575, 360581982237841448, 360581981752065464, 360581981726536859, 360581981727138008, 360581981652568131, 360581981577919314, 360581981317223961, 360581981574383523, 360581981888811467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518
