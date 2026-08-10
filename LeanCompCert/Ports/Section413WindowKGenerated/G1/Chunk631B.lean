import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631A

def state06 : KState := ⟨⟨362477713614291700, 362477772341912354⟩, ⟨480571151716913855, 483076530675100885⟩, true⟩

def words05 : List Nat := [371285420826412384, 371285420907937506, 371285420986715860, 371285420988909287, 371285420920127903, 371285420874471806, 371285421005992839, 371285421008141826, 371285420917367884, 371285420798699484]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483446102539550, 362483504849404966⟩, ⟨118515503025694541, 121022097577152611⟩, true⟩

def words06 : List Nat := [371285420679086440, 371285420662384491, 371285420713342780, 371285420853954768, 371285420955377437, 371285420957523501, 371285420724761750, 371285420629901301, 371285420663196999, 371285420665418535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482417829215422, 362482476595616732⟩, ⟨183474323299710487, 185982152030223563⟩, true⟩

def words07 : List Nat := [371285420636710491, 371285420610269007, 371285420682459272, 371285420684824205, 371285420661082778, 371285420648785927, 371285420635745230, 371285420622351976, 371285420326652278, 371285420282733387]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473409131294214, 362473467916831058⟩, ⟨752717736031312321, 755226773844746667⟩, true⟩

def words08 : List Nat := [371285420297212272, 371285420299396208, 371285420152695494, 371285420005876756, 371285419858196792, 371285419787382913, 371285419618386656, 371285419648157799, 371285419649810694, 371285419598645345]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497935841668825, 362497994646638264⟩, ⟨(-797268679710759374), (-794758413854370220)⟩, true⟩

def words09 : List Nat := [371285419410967188, 371285419410160621, 371285419568813011, 371285419570964618, 371285419475351187, 371285419301652670, 371285419201419726, 371285419203807721, 371285419352833739, 371285419554252790]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk631B
