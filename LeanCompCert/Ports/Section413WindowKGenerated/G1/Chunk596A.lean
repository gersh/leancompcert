import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505735138813568, 362505787193314006⟩, ⟨(-1235542516297255170), (-1233446857232691466)⟩, true⟩

def state01 : KState := ⟨⟨362480637270674119, 362480689343334991⟩, ⟨260400983537921577, 262497725060851779⟩, true⟩

def words00 : List Nat := [371285092470815760, 371285092532118821, 371285092797941804, 371285093064775416, 371285093325618328, 371285093327634846, 371285093213165851, 371285093070928183, 371285092927866988, 371285092928724370]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478529463160299, 362478581554005927⟩, ⟨386142004578043696, 388239830183692676⟩, true⟩

def words01 : List Nat := [371285093064283482, 371285093274546955, 371285093487829124, 371285093489846831, 371285093378464372, 371285093352336329, 371285093578399637, 371285093580426180, 371285093566877029, 371285093459913068]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362512156834117155, 362512208942984355⟩, ⟨(-1618855729838759543), (-1616756829693606271)⟩, true⟩

def words02 : List Nat := [371285093524703778, 371285093590731037, 371285093908343084, 371285094226784362, 371285094501114856, 371285094543300208, 371285094866606745, 371285095190925475, 371285095796007269, 371285096252778026]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502375285976258, 362502427413274227⟩, ⟨(-1035519938019211203), (-1033419938755488101)⟩, true⟩

def words03 : List Nat := [371285096662776105, 371285097073449973, 371285097599246393, 371285097985518327, 371285098455148094, 371285098925521966, 371285099393689975, 371285099487365849, 371285099779278762, 371285100072371904]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486817653792195, 362486869799057085⟩, ⟨(-107540226789191839), (-105439155885362427)⟩, true⟩

def words04 : List Nat := [371285100524440687, 371285100726153250, 371285100916647649, 371285101107795459, 371285101367265642, 371285101487663809, 371285101721733395, 371285101956620784, 371285102166523346, 371285102198247621]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596A
