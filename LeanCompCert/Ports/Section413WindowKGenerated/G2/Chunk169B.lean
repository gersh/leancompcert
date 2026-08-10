import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169A

def state06 : KState := ⟨⟨360515287676135133, 360515289320871085⟩, ⟨1147612365234794088, 1147631248623956436⟩, true⟩

def words05 : List Nat := [360582969131833948, 360582969419709097, 360582969419900021, 360582967952540219, 360582966778800116, 360582964697836846, 360582962617054532, 360582962485434782, 360582960247509549, 360582956257700328]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615567883271214, 360615569530034255⟩, ⟨(-553626443876165845), (-553607526097516479)⟩, true⟩

def words06 : List Nat := [360582952268316282, 360582948189995441, 360582948921355614, 360582951017795918, 360582951017996367, 360582950138863932, 360582948183245722, 360582946975322627, 360582946811715883, 360582948734200332]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603136827376344, 360603138476180539⟩, ⟨(-342794782959657501), (-342775830532406149)⟩, true⟩

def words07 : List Nat := [360582948907527043, 360582949080856796, 360582949737128039, 360582952911418691, 360582953362514555, 360582953813588961, 360582953813780101, 360582952518644554, 360582951442336056, 360582952631381505]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360654334506715210, 360654336157542741⟩, ⟨(-1212286291979916614), (-1212267305186313500)⟩, true⟩

def words08 : List Nat := [360582957273909152, 360582962053765889, 360582964044812556, 360582966035647170, 360582966353536236, 360582968939989268, 360582974978064581, 360582981015470201, 360582984344184283, 360582988543795092]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360735876642359200, 360735878295214164⟩, ⟨(-2598239809709952214), (-2598220788460130916)⟩, true⟩

def words09 : List Nat := [360582993736077795, 360582998927813272, 360583007568722271, 360583014465315215, 360583017849590729, 360583021233487324, 360583026150786195, 360583032786936560, 360583041778022765, 360583050768100458]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169B
