import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk345

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486335443309857, 362486352129213913⟩, ⟨(-54429041255787079), (-54039977061178941)⟩, true⟩

def state01 : KState := ⟨⟨362482989227977944, 362483005923859999⟩, ⟨61078369157660123, 61467777643817737⟩, true⟩

def words00 : List Nat := [371284786684823619, 371284786775714991, 371284786776566711, 371284786747338123, 371284786849827539, 371284786851072252, 371284786753524754, 371284786918567010, 371284787081114413, 371284787082296505]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362528448555336421, 362528465261331586⟩, ⟨(-1507924184690520772), (-1507534427148831074)⟩, true⟩

def words01 : List Nat := [371284787819576184, 371284788609014444, 371284790237505130, 371284790747672577, 371284791128752691, 371284791510136260, 371284792233765000, 371284792660818847, 371284793926717663, 371284795193049995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480024145289079, 362480040861389500⟩, ⟨163879555868814042, 164269662294637154⟩, true⟩

def words02 : List Nat := [371284796383405166, 371284796611341198, 371284797213314023, 371284797815850717, 371284798662638249, 371284798663757885, 371284798531267723, 371284798309411532, 371284798162815345, 371284798164091343]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470468251650116, 362470484977823508⟩, ⟨493930208354609172, 494320662652603766⟩, true⟩

def words03 : List Nat := [371284798231897401, 371284798437891998, 371284798637330480, 371284798638451113, 371284797895257202, 371284797408855879, 371284797272873328, 371284797274012567, 371284796932984224, 371284796519880619]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362506613267559462, 362506630003750599⟩, ⟨(-754646638762621948), (-754255838400849274)⟩, true⟩

def words04 : List Nat := [371284796236197750, 371284796237445374, 371284796696168775, 371284797345575010, 371284797799324405, 371284797800446138, 371284797675713155, 371284797995771147, 371284799153432114, 371284799786437038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503297334751856, 362503314081183931⟩, ⟨(-639996064211822392), (-639604909975963624)⟩, true⟩

def words05 : List Nat := [371284800239895032, 371284800693721899, 371284801907760968, 371284802805124636, 371284803958188492, 371284805111604133, 371284806262246628, 371284806456955512, 371284806993250888, 371284807530158904]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478778669954957, 362478795426366599⟩, ⟨207531588981504716, 207923088163899394⟩, true⟩

def words06 : List Nat := [371284808391670722, 371284808508435667, 371284808555064362, 371284808602057674, 371284808814963030, 371284808816218763, 371284809169112097, 371284809618509810, 371284809977944762, 371284809979104925]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509224280908665, 362509241047461735⟩, ⟨(-845162483094007542), (-844770633272421112)⟩, true⟩

def words07 : List Nat := [371284810394452395, 371284810984310397, 371284811679099384, 371284811680220861, 371284811391705202, 371284810980418711, 371284810879884901, 371284810881644025, 371284811588887720, 371284812296608018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484808889739032, 362484825666391284⟩, ⟨(-841783196516030), (-449584092474720)⟩, true⟩

def words08 : List Nat := [371284813001629077, 371284813002750635, 371284813019920710, 371284813447670820, 371284814130664878, 371284814131786497, 371284813700919628, 371284813078298847, 371284812667596445, 371284812669250627]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465982535454097, 362465999322221616⟩, ⟨650624490744004540, 651017039785567552⟩, true⟩

def words09 : List Nat := [371284813506402389, 371284814343979103, 371284815176882295, 371284815326923872, 371284815327719862, 371284815310800324, 371284815895339054, 371284815896461055, 371284815386148219, 371284814843602702]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk345
