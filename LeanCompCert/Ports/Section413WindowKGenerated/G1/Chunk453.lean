import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk453

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484866839947335, 362484896254882585⟩, ⟨27851698659039815, 28751995539500685⟩, true⟩

def state01 : KState := ⟨⟨362468932655343695, 362468962083633106⟩, ⟨749779404009481347, 750680305902781029⟩, true⟩

def words00 : List Nat := [371285531358693724, 371285531360193271, 371285531127036243, 371285530893908276, 371285530660184344, 371285530398221506, 371285529891664068, 371285529872550880, 371285529852953885, 371285529735495891]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508196991124685, 362508226433008864⟩, ⟨(-1029549961246168308), (-1028648443307727982)⟩, true⟩

def words01 : List Nat := [371285529370888601, 371285529210285870, 371285529332247743, 371285529333747825, 371285529027779341, 371285528678139714, 371285528463307679, 371285528479237944, 371285528981093757, 371285529483618786]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497437664523122, 362497467119925219⟩, ⟨(-541928117939328068), (-541025987298450536)⟩, true⟩

def words02 : List Nat := [371285529984930920, 371285530110717808, 371285530648743193, 371285531187520990, 371285531707933738, 371285531709434391, 371285531649708330, 371285531553045947, 371285531843841653, 371285532108844536]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472378244713551, 362472407713628146⟩, ⟨594211511917868701, 595114255150714063⟩, true⟩

def words03 : List Nat := [371285532515766916, 371285532923283366, 371285533300683287, 371285533302187418, 371285533198025031, 371285533221089873, 371285533729602885, 371285533731103889, 371285533591555909, 371285533303728515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362514567513703522, 362514596996057936⟩, ⟨(-1318781684841895149), (-1317878332179736277)⟩, true⟩

def words04 : List Nat := [371285533211934637, 371285533240748750, 371285533755025385, 371285534269917738, 371285534708609894, 371285534816814332, 371285535349551545, 371285535883025428, 371285536832822207, 371285537475161380]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500002693657294, 362500032189749497⟩, ⟨(-658190839202804068), (-657286863467148348)⟩, true⟩

def words05 : List Nat := [371285538117216134, 371285538759751107, 371285539430354530, 371285539859216713, 371285540410952211, 371285540963231520, 371285541513344716, 371285541514846541, 371285541736683037, 371285542058062208]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489143895399166, 362489173404851195⟩, ⟨(-165525426933213670), (-164620845125220184)⟩, true⟩

def words06 : List Nat := [371285542864226613, 371285543112386975, 371285543359402589, 371285543606910653, 371285543959307944, 371285544070112342, 371285544383307343, 371285544697094477, 371285544995858352, 371285545077392572]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362521947765277393, 362521977288293149⟩, ⟨(-1653995564369232841), (-1653090367105830225)⟩, true⟩

def words07 : List Nat := [371285545552694774, 371285546028740316, 371285546787894341, 371285547152667997, 371285547370502723, 371285547588806681, 371285548291835464, 371285548753301918, 371285549557067396, 371285550361449188]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502668335721604, 362502697872308189⟩, ⟨(-779118322830041593), (-778212509653687407)⟩, true⟩

def words08 : List Nat := [371285551068856108, 371285551129686519, 371285551508044587, 371285551887173115, 371285552355179062, 371285552388981130, 371285552390117018, 371285552382276418, 371285552849447337, 371285553228884302]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470285208714641, 362470314758840912⟩, ⟨691022721674295655, 691929149485731643⟩, true⟩

def words09 : List Nat := [371285553965275459, 371285554702261873, 371285555437926926, 371285555527387537, 371285555637252865, 371285555747845569, 371285556107851753, 371285556109354961, 371285555823008530, 371285555489005796]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk453
