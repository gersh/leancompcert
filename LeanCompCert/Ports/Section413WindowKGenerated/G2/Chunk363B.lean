import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363A

def state06 : KState := ⟨⟨360597840485465947, 360597848565704249⟩, ⟨(-579743202741920589), (-579544592050576527)⟩, true⟩

def words05 : List Nat := [360581909463749970, 360581908902899837, 360581908535937253, 360581909154127857, 360581909286093042, 360581909418128202, 360581909418563675, 360581909169914915, 360581909494953495, 360581909933872051]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569971957781016, 360569980042623770⟩, ⟨433566927391344307, 433765705523248969⟩, true⟩

def words06 : List Nat := [360581910597227921, 360581910597716898, 360581910506947511, 360581909800684469, 360581909094387559, 360581907870978951, 360581907297747958, 360581907164998179, 360581907032206706, 360581906512393450]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600845799996511, 360600853889463371⟩, ⟨(-689417209048996495), (-689218262715642787)⟩, true⟩

def words07 : List Nat := [360581906283596596, 360581906382858082, 360581907236243415, 360581907884385209, 360581907884836653, 360581907836780747, 360581907848137521, 360581908390801384, 360581908911970689, 360581909433216549]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360613915772958534, 360613923867082247⟩, ⟨(-1165263007840837634), (-1165063892067938394)⟩, true⟩

def words08 : List Nat := [360581909502945045, 360581909503434376, 360581908889940702, 360581908960482291, 360581908960892634, 360581908662875201, 360581908630145831, 360581908109410127, 360581907821125566, 360581908701462508]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546330477545399, 360546338576286165⟩, ⟨1294675526544477518, 1294874810355207118⟩, true⟩

def words09 : List Nat := [360581910153439887, 360581911605431188, 360581912480168306, 360581912931086150, 360581913019124464, 360581913107292613, 360581913448157514, 360581913448647106, 360581913036889157, 360581912060087133]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363B
