import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk045

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362518762613071533, 362518762849160080⟩, ⟨(-160603003636217096), (-160602283429880824)⟩, true⟩

def state01 : KState := ⟨⟨362351062326686922, 362351062563866833⟩, ⟨594428054471168846, 594428779594354790⟩, true⟩

def words00 : List Nat := [371283109342014375, 371283109342136649, 371283071931343832, 371283033415203208, 371282994916114899, 371282959310793434, 371282899336488002, 371282888415215873, 371282877498746867, 371282864954020792]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362751799951765132, 362751800190054425⟩, ⟨(-1215145900775500445), (-1215145170643341401)⟩, true⟩

def words01 : List Nat := [371282836927523970, 371282838118561197, 371282888195929474, 371282888196052214, 371282886141797508, 371282872006787400, 371282892579716923, 371282903272230058, 371282962762782364, 371283022227072045]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362687791056625576, 362687791296027245⟩, ⟨(-925439747759641972), (-925439012593848926)⟩, true⟩

def words02 : List Nat := [371283071653594256, 371283096208905962, 371283169494933378, 371283242748631357, 371283330372991787, 371283367815328929, 371283405270666348, 371283442709505263, 371283500123129069, 371283545210705275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362428693784646979, 362428694025159934⟩, ⟨250616646186100003, 250617386391707885⟩, true⟩

def words03 : List Nat := [371283624462367794, 371283703679112949, 371283782663573975, 371283797128964512, 371283825859597777, 371283854577631036, 371283913601668409, 371283913601791966, 371283908254234295, 371283896092647095]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513950728645044, 362513950970267373⟩, ⟨(-137270119257238506), (-137269374009376674)⟩, true⟩

def words04 : List Nat := [371283905316921420, 371283905317057454, 371283902721133262, 371283901606615407, 371283900492549194, 371283889531178357, 371283814447477999, 371283787538640342, 371283781876947598, 371283788506191483]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362521717755453438, 362521717998206552⟩, ⟨(-172426638906443384), (-172425888507944352)⟩, true⟩

def words05 : List Nat := [371283788506284513, 371283787022405160, 371283817268364897, 371283834810955469, 371283866541103636, 371283898257372068, 371283923163123127, 371283923163247263, 371283905303203494, 371283913593797882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362429305698137831, 362429305941996997⟩, ⟨249791609458565631, 249792364906545955⟩, true⟩

def words06 : List Nat := [371283969739933551, 371283969740057707, 371283962169970263, 371283954190116646, 371283946213711697, 371283940331410134, 371283928984883169, 371283947193675307, 371283965102679455, 371283965102808058]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362553300728131474, 362553300973117358⟩, ⟨(-317856268949540447), (-317855508346813519)⟩, true⟩

def words07 : List Nat := [371283960974785979, 371283968801214069, 371284005097555865, 371284005097680348, 371283978031440598, 371283941752121812, 371283905488603042, 371283903279726967, 371283900206964297, 371283915356800656]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362320235060287104, 362320235306399575⟩, ⟨750582230968545349, 750582996736798891⟩, true⟩

def words08 : List Nat := [371283930675331946, 371283930675456817, 371283913018816568, 371283927873145471, 371283943991119188, 371283943991244056, 371283897088909605, 371283841739565177, 371283786414294614, 371283761013749641]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362337468554782920, 362337468802023989⟩, ⟨672146434414238243, 672147205368499183⟩, true⟩

def words09 : List Nat := [371283737007647589, 371283748615298591, 371283759956187069, 371283759956312113, 371283708498071651, 371283670990807242, 371283643091968484, 371283643092094676, 371283619531468974, 371283587759712794]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk045
