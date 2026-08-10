import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202A

def state06 : KState := ⟨⟨360580053089165315, 360580055474417487⟩, ⟨43343989385077543, 43376692759634465⟩, true⟩

def words05 : List Nat := [360582195328558530, 360582196155796825, 360582196156028270, 360582195514273863, 360582195514491343, 360582194972406046, 360582195450540380, 360582196581213621, 360582196581447152, 360582196476034449]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360670327992523071, 360670330380227536⟩, ⟨(-1785963641657394254), (-1785930888587032716)⟩, true⟩

def words06 : List Nat := [360582198690239418, 360582202876532985, 360582208151269227, 360582213425534944, 360582216431780645, 360582217012951530, 360582218294832390, 360582219576664209, 360582223281360270, 360582227628089653]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559717765770782, 360559720155954468⟩, ⟨456727315442161080, 456760118778400266⟩, true⟩

def words07 : List Nat := [360582230429939993, 360582233231546583, 360582235161271472, 360582238431408444, 360582241034750570, 360582243637878203, 360582245007362444, 360582245007622591, 360582243954600545, 360582242844257151]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567264851421383, 360567267244054133⟩, ⟨303397068179097351, 303429921194656549⟩, true⟩

def words08 : List Nat := [360582241733936762, 360582241412156459, 360582238668504134, 360582234709034102, 360582230749910406, 360582226179090563, 360582223598237874, 360582223436265047, 360582223274279764, 360582221897636916]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610711585925980, 360610713981019637⟩, ⟨(-578617448227397850), (-578584545268488460)⟩, true⟩

def words09 : List Nat := [360582222170363680, 360582223180076617, 360582223180291815, 360582223035502473, 360582221329526919, 360582217097165547, 360582212865171399, 360582211049881743, 360582212279007810, 360582213683237829]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202B
