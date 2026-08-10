import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396A

def state06 : KState := ⟨⟨360587912822484262, 360587922504403114⟩, ⟨(-216125491234794538), (-215865959474993974)⟩, true⟩

def words05 : List Nat := [360582477808346710, 360582478079584428, 360582478625264119, 360582479495094266, 360582479752328396, 360582480009626337, 360582480010104583, 360582479949545594, 360582479590037310, 360582479727885251]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606554719150491, 360606564406132189⟩, ⟨(-955576904700905271), (-955317172123251669)⟩, true⟩

def words06 : List Nat := [360582480074993833, 360582480437527319, 360582480438012758, 360582480406490303, 360582480374881557, 360582480484253434, 360582481420121608, 360582482356045583, 360582482803052460, 360582483410641195]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360654731791429253, 360654741483481802⟩, ⟨(-2867045338168106429), (-2866785404405232521)⟩, true⟩

def words07 : List Nat := [360582484652125225, 360582485893711208, 360582487582526506, 360582488822103068, 360582489468926006, 360582490115768898, 360582490857957907, 360582492045650378, 360582493866887029, 360582495688153932]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593601588998041, 360593611286176526⟩, ⟨(-441279555672130338), (-441019418487437360)⟩, true⟩

def words08 : List Nat := [360582497190036655, 360582498060115017, 360582498912765530, 360582499765522937, 360582500457899731, 360582500518609671, 360582500519088160, 360582500262408560, 360582500005637522, 360582499965764155]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360520562797061772, 360520572499295375⟩, ⟨2458114917119060140, 2458375254966930576⟩, true⟩

def words09 : List Nat := [360582500520839110, 360582501075988053, 360582501244013325, 360582501244550713, 360582500987912672, 360582500361690925, 360582499735351040, 360582498945019846, 360582497868520290, 360582496309244165]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396B
