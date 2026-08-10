import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810A

def state06 : KState := ⟨⟨362490279534079705, 362490378162685831⟩, ⟨(-427255243812107338), (-421856739402237146)⟩, true⟩

def words05 : List Nat := [371285172643181997, 371285172823340391, 371285173065267865, 371285173254497961, 371285173456698874, 371285173660005650, 371285173851146584, 371285173853951455, 371285173906290775, 371285173973995805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480639563955899, 362480738217511108⟩, ⟨354223708481524277, 359624235396371583⟩, true⟩

def words06 : List Nat := [371285174174482808, 371285174177287944, 371285174175190888, 371285174173734813, 371285174205802952, 371285174208895042, 371285174179070084, 371285174186944302, 371285174189041670, 371285174189330479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501527017839029, 362501625696763269⟩, ⟨(-1339229087791595226), (-1333826504079670282)⟩, true⟩

def words07 : List Nat := [371285174233902755, 371285174334714627, 371285174495056610, 371285174530135941, 371285174532313386, 371285174528861041, 371285174669910071, 371285174742557624, 371285174947358319, 371285175153429077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491153630385436, 362491252334686939⟩, ⟨(-498154521073341999), (-492749879648667059)⟩, true⟩

def words08 : List Nat := [371285175315131084, 371285175317937240, 371285175424192115, 371285175555731370, 371285175732657354, 371285175735463298, 371285175709828047, 371285175678898141, 371285175751354345, 371285175829530403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492625909210958, 362492724638734961⟩, ⟨(-617511673572087262), (-612104986726557764)⟩, true⟩

def words09 : List Nat := [371285176043252587, 371285176258113564, 371285176472046033, 371285176541206250, 371285176613211932, 371285176686597051, 371285176910508786, 371285177006676535, 371285177101859616, 371285177198053261]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810B
