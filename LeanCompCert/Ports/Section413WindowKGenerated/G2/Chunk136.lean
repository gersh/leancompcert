import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk136

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360543864018800583, 360543865054956964⟩, ⟨518178097595001132, 518187641236217656⟩, true⟩

def state01 : KState := ⟨⟨360529454202230559, 360529455239980041⟩, ⟨714084689925302619, 714094255240700551⟩, true⟩

def words00 : List Nat := [360581964286125649, 360581959141228112, 360581957617533973, 360581958497354170, 360581958497509534, 360581954734705553, 360581945608851327, 360581937247182187, 360581928886688063, 360581923590842694]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551385434490819, 360551386473846319⟩, ⟨415324397793715320, 415333984975068252⟩, true⟩

def words01 : List Nat := [360581919736144643, 360581912356042632, 360581904976992734, 360581903688949346, 360581903689093046, 360581900672651128, 360581897656635338, 360581890736531790, 360581883131630224, 360581880892713799]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360614736337979909, 360614737378928361⟩, ⟨(-447810990408740237), (-447801381523421777)⟩, true⟩

def words02 : List Nat := [360581879791048996, 360581881456885456, 360581881457036267, 360581879732601766, 360581878008392341, 360581874707447560, 360581878955815963, 360581883758983842, 360581883759137960, 360581885689285384]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360732707629368911, 360732708671912984⟩, ⟨(-2056327884060275699), (-2056318253418652225)⟩, true⟩

def words03 : List Nat := [360581891293858617, 360581896897658742, 360581907854519988, 360581917206113279, 360581921754113298, 360581926301460876, 360581932365545702, 360581941148070205, 360581952201544858, 360581963253437898]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360676624296272428, 360676625340428764⟩, ⟨(-1291788845783207023), (-1291779193142382415)⟩, true⟩

def words04 : List Nat := [360581971604920178, 360581977874972613, 360581983945757762, 360581990015701652, 360581994722838519, 360581994723007740, 360581994102563365, 360581990789203153, 360581989501906498, 360581996434623887]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360378186437769982, 360378187483518761⟩, ⟨2783496011361733161, 2783505685747616489⟩, true⟩

def words05 : List Nat := [360582001199349751, 360582005963408598, 360582006750321568, 360582006750490865, 360582002215045835, 360581996323635085, 360581990433040259, 360581984351305338, 360581972949757509, 360581958031523711]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360496277079861408, 360496278127210222⟩, ⟨1169719296356379401, 1169728992606657055⟩, true⟩

def words06 : List Nat := [360581943115436332, 360581930427782354, 360581922203272854, 360581915504948756, 360581908807588925, 360581897513442535, 360581880904891343, 360581867888546176, 360581854874055843, 360581847182997103]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360498792110596893, 360498793159563952⟩, ⟨1134955225998352479, 1134964944377837591⟩, true⟩

def words07 : List Nat := [360581840923986476, 360581830595836048, 360581820269165069, 360581810302811824, 360581803732310951, 360581795615709643, 360581787500276129, 360581775879981880, 360581764498237027, 360581758433275783]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360484678187110497, 360484679237675076⟩, ⟨1327940408199487154, 1327950148441109536⟩, true⟩

def words08 : List Nat := [360581752369143476, 360581751620218909, 360581745567765285, 360581736834714852, 360581728102915054, 360581713944013690, 360581702489931500, 360581696346866744, 360581690204683109, 360581680709438488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603114740042374, 360603115792211801⟩, ⟨(-293785176674755626), (-293775414454752320)⟩, true⟩

def words09 : List Nat := [360581673624522204, 360581671847682194, 360581673600756294, 360581674493682281, 360581674493839848, 360581670235168168, 360581667022945013, 360581670765656092, 360581672331126749, 360581673896404579]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk136
