import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597736071336592, 360597796954475031⟩, ⟨(-1496366109005376413), (-1492419437111887075)⟩, true⟩

def state01 : KState := ⟨⟨360592419222454969, 360592480118692466⟩, ⟨(-985904842831418319), (-981956913360583589)⟩, true⟩

def words00 : List Nat := [360582251352229396, 360582251573842649, 360582251741307949, 360582251908910296, 360582251984005223, 360582252113474258, 360582252248678261, 360582252384152687, 360582252464784112, 360582252572751266]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601335427130391, 360601396336531820⟩, ⟨(-1841958199576585293), (-1838009006173815273)⟩, true⟩

def words01 : List Nat := [360582252756789018, 360582252941274824, 360582253233840174, 360582253451335271, 360582253565739597, 360582253680253167, 360582253903020728, 360582254195336541, 360582254395846597, 360582254596639778]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608720618632919, 360608781541300909⟩, ⟨(-2551231515985337102), (-2547281048664633884)⟩, true⟩

def words02 : List Nat := [360582254730153582, 360582254800452597, 360582254956978179, 360582255113909675, 360582255208950367, 360582255338599307, 360582255413426357, 360582255488404078, 360582255651436206, 360582255929272870]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583280450621214, 360583341386412177⟩, ⟨(-108091592870033072), (-104139865285101980)⟩, true⟩

def words03 : List Nat := [360582256209113049, 360582256489208969, 360582256670356601, 360582256743516107, 360582256788753458, 360582256834359805, 360582256966511192, 360582257033944999, 360582257046489014, 360582257059246851]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595762324202459, 360595823273139071⟩, ⟨(-1306926292983228269), (-1302973302825545111)⟩, true⟩

def words04 : List Nat := [360582257088094706, 360582257171332701, 360582257362617083, 360582257554171316, 360582257653292616, 360582257654685537, 360582257645581864, 360582257634236811, 360582257698522897, 360582257841203688]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598907852502543, 360598968814696775⟩, ⟨(-1609063327889432199), (-1605109064270896559)⟩, true⟩

def words05 : List Nat := [360582257921402680, 360582258001762643, 360582258190276446, 360582258463341166, 360582258708343421, 360582258953568032, 360582259128423072, 360582259195347342, 360582259370423026, 360582259545958464]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589020353144216, 360589081328479977⟩, ⟨(-659280388194341524), (-655324862135864832)⟩, true⟩

def words06 : List Nat := [360582259718412210, 360582259821610646, 360582259826851342, 360582259832238217, 360582259833403986, 360582259845117060, 360582259916577482, 360582259988325529, 360582260000267514, 360582260072719802]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613919123939711, 360613980112414142⟩, ⟨(-3051467557095064397), (-3047510768738989037)⟩, true⟩

def words07 : List Nat := [360582260196101905, 360582260319889211, 360582260532932922, 360582260734624842, 360582260831953644, 360582260929352412, 360582261084630308, 360582261307935148, 360582261639190395, 360582261970755136]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592446863299598, 360592507865060849⟩, ⟨(-988339124731962645), (-984381059711754967)⟩, true⟩

def words08 : List Nat := [360582262247560537, 360582262527048455, 360582262793026289, 360582263059418841, 360582263256018704, 360582263368206523, 360582263425699397, 360582263483343361, 360582263498191488, 360582263606392382]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582511746742825, 360582572761627666⟩, ⟨(-33572203555763478), (-29612877424467128)⟩, true⟩

def words09 : List Nat := [360582263804193175, 360582264002257151, 360582264145566069, 360582264238727463, 360582264304040189, 360582264369766154, 360582264543358987, 360582264609246762, 360582264613694784, 360582264618346905]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960
