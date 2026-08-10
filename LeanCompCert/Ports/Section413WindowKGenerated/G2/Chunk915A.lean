import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598883232963941, 360598938335954556⟩, ⟨(-1554254140508926715), (-1550849468334961535)⟩, true⟩

def state01 : KState := ⟨⟨360589189678433759, 360589244793872428⟩, ⟨(-667253575523942452), (-663847764290067946)⟩, true⟩

def words00 : List Nat := [360581989603076521, 360581989740499434, 360581989816851472, 360581989893360479, 360581989939699793, 360581990058761860, 360581990213448784, 360581990368380831, 360581990418508114, 360581990499150591]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595743103755123, 360595798231700466⟩, ⟨(-1267064174414081263), (-1263657218632641793)⟩, true⟩

def words01 : List Nat := [360581990528854865, 360581990558940939, 360581990707904257, 360581990737915556, 360581990739135439, 360581990667721989, 360581990596058016, 360581990634990842, 360581990786929817, 360581990939181453]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583315619022444, 360583370759560298⟩, ⟨(-129741890455511726), (-126333782145290198)⟩, true⟩

def words02 : List Nat := [360581991031808398, 360581991039847590, 360581991100289175, 360581991161117152, 360581991162244697, 360581991140276047, 360581990998988896, 360581990797937554, 360581990596633382, 360581990530106394]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555601170283089, 360555656323291330⟩, ⟨2407103993168846797, 2410513242956338539⟩, true⟩

def words03 : List Nat := [360581990531842198, 360581990533847521, 360581990535031682, 360581990461366810, 360581990268328653, 360581990045752029, 360581989822791600, 360581989698174045, 360581989504966892, 360581989218669923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594184038102239, 360594239203603579⟩, ⟨(-1124949289742969616), (-1121538896276695292)⟩, true⟩

def words04 : List Nat := [360581988932076947, 360581988765100447, 360581988694222005, 360581988696012300, 360581988697235884, 360581988582206505, 360581988525801068, 360581988536773956, 360581988640830947, 360581988776013748]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915A
