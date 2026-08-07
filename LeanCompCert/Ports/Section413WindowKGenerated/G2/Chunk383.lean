import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360647444943150271, 360647453946772905⟩, ⟨(-2508421962385351499), (-2508188873450607927)⟩, true⟩

def state01 : KState := ⟨⟨360644163255248253, 360644172263794834⟩, ⟨(-2382872919558583767), (-2382639642012211469)⟩, true⟩

def words00 : List Nat := [360581968931032064, 360581970062920905, 360581971874717976, 360581973686588217, 360581975197284297, 360581976212054048, 360581976882334342, 360581977552636325, 360581978589438272, 360581980213417339]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600155928879513, 360600164942304649⟩, ⟨(-696887364337564195), (-696653899869945713)⟩, true⟩

def words01 : List Nat := [360581981540907957, 360581982868419156, 360581983631360091, 360581983717425874, 360581983717858967, 360581983483065797, 360581983692454742, 360581984563430998, 360581985038327783, 360581985513274354]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659022536649697, 360659031554957734⟩, ⟨(-2952947051969024553), (-2952713400364314109)⟩, true⟩

def words02 : List Nat := [360581986667659523, 360581988168192299, 360581989961382781, 360581991754583850, 360581992911450193, 360581993391756693, 360581994551308582, 360581995710951470, 360581997549716505, 360581999559957231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360627627005276548, 360627636028524090⟩, ⟨(-1749308676643779027), (-1749074835683673011)⟩, true⟩

def words03 : List Nat := [360582001231176046, 360582002902369211, 360582005252594820, 360582007941120548, 360582009946764031, 360582011952383167, 360582013522838315, 360582014732327808, 360582015922667550, 360582017113115424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360652848707749947, 360652857735874170⟩, ⟨(-2716534885524005356), (-2716300857567927544)⟩, true⟩

def words04 : List Nat := [360582018621878783, 360582019844279253, 360582020725552281, 360582021606836021, 360582022315776788, 360582023644309158, 360582025378413109, 360582027112525495, 360582028508279697, 360582030355686746]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360672940441807240, 360672949474823924⟩, ⟨(-3487190845708524526), (-3486956630102265652)⟩, true⟩

def words05 : List Nat := [360582032881347170, 360582035407029205, 360582037913778936, 360582039944853101, 360582041397514704, 360582042850141395, 360582044379254120, 360582046253491470, 360582048623650244, 360582050993811900]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600606224095364, 360600615262043907⟩, ⟨(-712244474983852902), (-712010070166954518)⟩, true⟩

def words06 : List Nat := [360582052956259753, 360582054243687982, 360582055668896888, 360582057094181995, 360582058347299261, 360582058925532593, 360582058930718064, 360582058935950200, 360582058936370596, 360582059319530891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597610870434964, 360597619913262600⟩, ⟨(-597146889597566257), (-596912297545558619)⟩, true⟩

def words07 : List Nat := [360582060481312572, 360582061643133055, 360582062464242734, 360582063301241268, 360582063939946531, 360582064578763214, 360582065894966110, 360582066815578718, 360582067221283004, 360582067627039064]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636611882162039, 360636620929887998⟩, ⟨(-2094260034896017426), (-2094025254821754354)⟩, true⟩

def words08 : List Nat := [360582068014210053, 360582068738740837, 360582069990764160, 360582071242821491, 360582071908346877, 360582072346373662, 360582073102947441, 360582073859642770, 360582074816953483, 360582076238298257]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611511222041789, 360611520274697261⟩, ⟨(-1130436420323468221), (-1130201450980091115)⟩, true⟩

def words09 : List Nat := [360582077241735075, 360582078245176340, 360582079925433863, 360582081975734357, 360582083563139507, 360582085150539606, 360582086397630296, 360582087177745602, 360582087944652979, 360582088711691608]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383
