import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998A

def state06 : KState := ⟨⟨360596548656746827, 360596614735096118⟩, ⟨(-1420224495686082347), (-1415768986498868703)⟩, true⟩

def words05 : List Nat := [360582437205870279, 360582437250272673, 360582437324111704, 360582437325564123, 360582437299553206, 360582437179111434, 360582437058393657, 360582437052024157, 360582437195173670, 360582437338650070]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595406675224605, 360595472767423692⟩, ⟨(-1306203133575707425), (-1301746241279311019)⟩, true⟩

def words06 : List Nat := [360582437431641800, 360582437529062892, 360582437684714198, 360582437840807263, 360582437971101590, 360582438118672367, 360582438215815241, 360582438313114890, 360582438358624415, 360582438490794047]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577133214384542, 360577199320263444⟩, ⟨518911408498159261, 523369667063582425⟩, true⟩

def words07 : List Nat := [360582438722700564, 360582438954881060, 360582439132561024, 360582439210370651, 360582439221166720, 360582439232372870, 360582439343334530, 360582439354564649, 360582439355864875, 360582439304915663]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585271777822518, 360585337897417527⟩, ⟨(-294000554558239588), (-289540925959297660)⟩, true⟩

def words08 : List Nat := [360582439301372823, 360582439407347495, 360582439479672746, 360582439552252040, 360582439553591683, 360582439541051811, 360582439428237902, 360582439384193879, 360582439339726174, 360582439328718052]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579737106737746, 360579803240178417⟩, ⟨258883091682179594, 263344103389695322⟩, true⟩

def words09 : List Nat := [360582439330033263, 360582439283724250, 360582439271914411, 360582439358373562, 360582439419066979, 360582439479996446, 360582439481313730, 360582439452607613, 360582439341999236, 360582439317289425]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998B
