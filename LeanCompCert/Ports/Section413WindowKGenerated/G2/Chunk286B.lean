import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286A

def state06 : KState := ⟨⟨360586195780868417, 360586200701786743⟩, ⟨(-109044944193455158), (-108949558296701434)⟩, true⟩

def words05 : List Nat := [360582396261526147, 360582398097680284, 360582399326375025, 360582399344811839, 360582399345130726, 360582398559136565, 360582398200982441, 360582399118368236, 360582399251349852, 360582399384376440]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360721459937850003, 360721464862339925⟩, ⟨(-3986382719752705938), (-3986287231476612202)⟩, true⟩

def words06 : List Nat := [360582400731320915, 360582402924406544, 360582406331155529, 360582409737739162, 360582412031278459, 360582414149503129, 360582417194737785, 360582420239870646, 360582424498101580, 360582429348005699]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360670190052232657, 360670194980334302⟩, ⟨(-2516088081570251205), (-2515992489728699391)⟩, true⟩

def words07 : List Nat := [360582433454590963, 360582437560936895, 360582442465290471, 360582448095018601, 360582453023383690, 360582457951466112, 360582461922484569, 360582465543775665, 360582468602994557, 360582471662119153]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360663538537665019, 360663543469331968⟩, ⟨(-2325554632527124900), (-2325458938414609760)⟩, true⟩

def words08 : List Nat := [360582474553909446, 360582476237464377, 360582477302486032, 360582478367471734, 360582479123821587, 360582480805333441, 360582483698646989, 360582486591833748, 360582488783041060, 360582491608524935]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360665608949230890, 360665613884479326⟩, ⟨(-2385103940183948340), (-2385008143300395944)⟩, true⟩

def words09 : List Nat := [360582494780309750, 360582497951986640, 360582501094399068, 360582503029151094, 360582503928267528, 360582504827351994, 360582506937539648, 360582509659118711, 360582512555044958, 360582515450860275]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk286B
