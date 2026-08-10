import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795A

def state06 : KState := ⟨⟨360571751564063406, 360571792775021556⟩, ⟨827143754444176956, 829358164463135030⟩, true⟩

def words05 : List Nat := [360582217637263463, 360582217626670633, 360582217615854947, 360582217692966387, 360582217693934825, 360582217663703673, 360582217633350899, 360582217503339179, 360582217215493492, 360582217085786553]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584873066730196, 360584914288404877⟩, ⟨(-216850192602178362), (-214634929921537262)⟩, true⟩

def words06 : List Nat := [360582216982391520, 360582217014503042, 360582217015523337, 360582216928508883, 360582216841311271, 360582216715052850, 360582216779718325, 360582216877839362, 360582216878881172, 360582216886965640]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603074632892423, 360603115865309034⟩, ⟨(-1665268760587455566), (-1663052643119129596)⟩, true⟩

def words07 : List Nat := [360582217030188738, 360582217173744470, 360582217363897207, 360582217530370697, 360582217563237601, 360582217596211929, 360582217622517003, 360582217728738315, 360582217992263430, 360582218256041507]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586577793047687, 360586619036309121⟩, ⟨(-352527488423808192), (-350310507870397214)⟩, true⟩

def words08 : List Nat := [360582218421902086, 360582218430351567, 360582218434659057, 360582218439284263, 360582218440242933, 360582218340337992, 360582218193899998, 360582217942594941, 360582217691078302, 360582217652888001]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548510724678062, 360548551978654923⟩, ⟨2677477447643234533, 2679695281089976829⟩, true⟩

def words09 : List Nat := [360582217710409444, 360582217768145073, 360582217769159303, 360582217733158481, 360582217644695728, 360582217517232542, 360582217389433194, 360582217230493820, 360582216913983426, 360582216492236456]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795B
