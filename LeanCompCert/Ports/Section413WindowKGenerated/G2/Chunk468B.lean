import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468A

def state06 : KState := ⟨⟨360601106714776186, 360601120417215491⟩, ⟨(-854777655253958935), (-854343759927892693)⟩, true⟩

def words05 : List Nat := [360582887569643146, 360582887238742266, 360582887030574646, 360582887442862258, 360582887740029616, 360582888037289345, 360582888107232456, 360582888192478873, 360582888582077977, 360582888971878689]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596077331291626, 360596091039783562⟩, ⟨(-619123081470016247), (-618688902487207289)⟩, true⟩

def words06 : List Nat := [360582889815627250, 360582890205209257, 360582890298957592, 360582890392767305, 360582890393317851, 360582890088604257, 360582890445176171, 360582890850865878, 360582890934519410, 360582891216812275]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609646404768980, 360609660119348297⟩, ⟨(-1255208881605889110), (-1254774417277754336)⟩, true⟩

def words07 : List Nat := [360582891570695834, 360582891924769639, 360582892479331955, 360582892828568308, 360582892829162545, 360582892791682372, 360582893169835850, 360582893881302258, 360582894452784273, 360582895024378528]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360645377604948400, 360645391325659963⟩, ⟨(-2930649498548330491), (-2930214746709598813)⟩, true⟩

def words08 : List Nat := [360582895365805935, 360582895641313059, 360582896275765219, 360582896910379112, 360582897430193876, 360582898148071490, 360582898638915935, 360582899129809911, 360582900074189375, 360582901407622182]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584826631071239, 360584840357856568⟩, ⟨(-91079163209018118), (-90644126541867706)⟩, true⟩

def words09 : List Nat := [360582902874581687, 360582904341600950, 360582905357911636, 360582905920516107, 360582906319217831, 360582906718073095, 360582907327042627, 360582907604800579, 360582907646590276, 360582907688477624]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468B
