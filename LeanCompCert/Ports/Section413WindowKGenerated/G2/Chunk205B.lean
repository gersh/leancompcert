import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205A

def state06 : KState := ⟨⟨360436118142828550, 360436120602427473⟩, ⟨2997560866806936654, 2997595087625101560⟩, true⟩

def words05 : List Nat := [360581956826300400, 360581955068148403, 360581953310136113, 360581949755060587, 360581944877284182, 360581939403408165, 360581933929985180, 360581929989446667, 360581925120254675, 360581918028868383]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360631073700839817, 360631076162930913⟩, ⟨(-1011834845109995392), (-1011800573040590646)⟩, true⟩

def words06 : List Nat := [360581910938112595, 360581905078071637, 360581900803665565, 360581898884787106, 360581896966076675, 360581893042200634, 360581890142899059, 360581888908116821, 360581887996731926, 360581890388148910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554688676793988, 360554691141402259⟩, ⟨559861582276548731, 559895906136493493⟩, true⟩

def words07 : List Nat := [360581891597661948, 360581892807086456, 360581893959448655, 360581896387223379, 360581898163445526, 360581899939537847, 360581900292436879, 360581900292701087, 360581898289458000, 360581896967745141]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360492402583568433, 360492405050662575⟩, ⟨1841909115910468599, 1841943490942206663⟩, true⟩

def words08 : List Nat := [360581895646069926, 360581894665258818, 360581892465557942, 360581889069054627, 360581885672838377, 360581880958689816, 360581877633099962, 360581873217886730, 360581868803073506, 360581863209523295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360634417349910172, 360634419819500136⟩, ⟨(-1082993136194517573), (-1082958709761280981)⟩, true⟩

def words09 : List Nat := [360581858865210099, 360581855986171110, 360581853107328738, 360581852575982656, 360581852149756047, 360581849698449944, 360581847247330919, 360581846455753656, 360581849008072691, 360581851560203924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205B
