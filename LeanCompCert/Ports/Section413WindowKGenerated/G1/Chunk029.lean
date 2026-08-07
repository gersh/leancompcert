import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk029

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362912319658882686, 362912319752577068⟩, ⟨(-1242956566656650905), (-1242956382263780735)⟩, true⟩

def state01 : KState := ⟨⟨362568195670910977, 362568195765286654⟩, ⟨(-244362402372696589), (-244362216000510877)⟩, true⟩

def words00 : List Nat := [371284007360877352, 371284007360953024, 371284102160372099, 371284208838343191, 371284323736655774, 371284323736731536, 371284281530307814, 371284222380666132, 371284222495097187, 371284251342064219]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362292847843980207, 362292847939041587⟩, ⟨559754604173687901, 559754792544737097⟩, true⟩

def words01 : List Nat := [371284358008583433, 371284464601901079, 371284569524108828, 371284569524184936, 371284558427865606, 371284551564381294, 371284655516150714, 371284655516226851, 371284610457813110, 371284544785803484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362751457333602131, 362751457429346853⟩, ⟨(-781176055126659934), (-781175864756737938)⟩, true⟩

def words02 : List Nat := [371284488718784611, 371284488718868421, 371284475842833356, 371284510519781102, 371284534353802452, 371284534353880753, 371284594274798752, 371284682578543500, 371284844506142552, 371284935469347966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362777454025175280, 362777454121617473⟩, ⟨(-857722150205458523), (-857721957788360403)⟩, true⟩

def words03 : List Nat := [371285024670419871, 371285113810690965, 371285247416016658, 371285325207572439, 371285434329924047, 371285543377996665, 371285629230069266, 371285629230146391, 371285711959009258, 371285811157391577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362364697592410737, 362364697689537247⟩, ⟨358225096690518475, 358225291123085117⟩, true⟩

def words04 : List Nat := [371285977842152264, 371285991304733512, 371286005273884855, 371286019233575761, 371286060018730230, 371286060018814781, 371286073538315778, 371286102570345082, 371286129991533126, 371286129991612870]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362978180889704569, 362978180987528772⟩, ⟨(-1454390205714879761), (-1454390009220576023)⟩, true⟩

def words05 : List Nat := [371286115410635284, 371286141961247123, 371286283043692201, 371286332480471748, 371286368506728244, 371286404508641194, 371286554896790510, 371286666959263651, 371286833011353213, 371286998951317838]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362699121444597030, 362699121543121512⟩, ⟨(-628529337391000470), (-628529138820343282)⟩, true⟩

def words06 : List Nat := [371287140749169511, 371287140749246939, 371287235936831983, 371287340397413254, 371287475481119916, 371287475481197503, 371287459826628825, 371287433915764679, 371287495570365165, 371287566801007631]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362294672278202261, 362294672377424203⟩, ⟨576555376598337083, 576555577244067891⟩, true⟩

def words07 : List Nat := [371287751331389185, 371287935737663825, 371288118475360546, 371288151152906894, 371288170175324622, 371288189185000621, 371288275540407363, 371288275540485149, 371288212349558084, 371288147403345032]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362292754842467677, 362292754942388210⟩, ⟨583206660515865486, 583206863246996794⟩, true⟩

def words08 : List Nat := [371288082500672409, 371288071841942290, 371288048054241957, 371288074129013464, 371288087397083494, 371288087397161590, 371287952029434485, 371287891087793789, 371287830186891505, 371287807405012624]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362309412077791387, 362309412178425491⟩, ⟨533660844839679067, 533661049707991119⟩, true⟩

def words09 : List Nat := [371287742191944268, 371287675845873972, 371287620463583934, 371287620463670028, 371287576708770181, 371287564016989311, 371287551333651877, 371287528547711146, 371287358510341581, 371287299194994822]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk029
