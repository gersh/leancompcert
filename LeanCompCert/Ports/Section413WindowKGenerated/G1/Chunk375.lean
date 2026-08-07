import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk375

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463881091781623, 362463900941980889⟩, ⟨784367387585339860, 784870437975339938⟩, true⟩

def state01 : KState := ⟨⟨362480330027481430, 362480349888584644⟩, ⟨167471385088993047, 167974844432732647⟩, true⟩

def words00 : List Nat := [371284830416083400, 371284830417310346, 371284829849470668, 371284829290266156, 371284828730610249, 371284828290241724, 371284827801045597, 371284827912862002, 371284828022323810, 371284828023600180]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504056510897944, 362504076383090426⟩, ⟨(-722635106219059678), (-722131230862250804)⟩, true⟩

def words01 : List Nat := [371284828496537005, 371284829089481331, 371284829843500371, 371284829844724529, 371284829651788204, 371284829274020864, 371284829227400729, 371284829299873477, 371284829813688585, 371284830328058251]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482386623228784, 362482406506459008⟩, ⟨90423928013931299, 90928217563312829⟩, true⟩

def words02 : List Nat := [371284830693488177, 371284830694712724, 371284830378155330, 371284830530625068, 371284830837362913, 371284830838588549, 371284830381986947, 371284829791583620, 371284829319265933, 371284829320675990]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475915182823177, 362475935077069399⟩, ⟨333439006232215901, 333943709267640601⟩, true⟩

def words03 : List Nat := [371284829665499901, 371284830075348375, 371284830482957176, 371284830484203399, 371284830349551947, 371284830389873666, 371284831139418497, 371284831140643299, 371284830989535822, 371284830753927888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481832244359028, 362481852149581470⟩, ⟨111265173957134920, 111770289095786364⟩, true⟩

def words04 : List Nat := [371284830519273420, 371284830520622428, 371284830175714644, 371284830183092356, 371284830184040195, 371284830080319140, 371284829030828013, 371284828691607881, 371284828720591681, 371284828721860985]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467199840210282, 362467219756597213⟩, ⟨660833449532334302, 661338983954298416⟩, true⟩

def words05 : List Nat := [371284828643509394, 371284828563770932, 371284828777205161, 371284828819648975, 371284828820525800, 371284828770102258, 371284828719292532, 371284828661018639, 371284827758050605, 371284827290781300]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472369340871856, 362472389268191730⟩, ⟨466706127556127769, 467212072676577007⟩, true⟩

def words06 : List Nat := [371284827063150771, 371284827064397379, 371284826720246589, 371284826366707666, 371284826012735839, 371284825704011430, 371284825084394647, 371284825130005230, 371284825130937398, 371284825043349478]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362521283911402282, 362521303849776058⟩, ⟨(-1371246896102193852), (-1370740535630451288)⟩, true⟩

def words07 : List Nat := [371284825091067619, 371284825470381244, 371284826557872010, 371284826701556944, 371284826716183565, 371284826731224156, 371284827346496919, 371284827609902975, 371284828581363966, 371284829553306288]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489968979003712, 362489988928461313⟩, ⟨(-194351869117282479), (-193845092060815523)⟩, true⟩

def words08 : List Nat := [371284830522756354, 371284830966440508, 371284831524736330, 371284832083650516, 371284832854429433, 371284832855655592, 371284832682957881, 371284832253501298, 371284832100966971, 371284832239571398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468654639007659, 362468674599511388⟩, ⟨607094448460321308, 607601640796657060⟩, true⟩

def words09 : List Nat := [371284833085671518, 371284833932236462, 371284834780748634, 371284834781975245, 371284834758634184, 371284834831478882, 371284835052770553, 371284835054005651, 371284834646008946, 371284834217617683]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk375
