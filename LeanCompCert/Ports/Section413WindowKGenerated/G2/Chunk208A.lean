import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360501198957550138, 360501201477458418⟩, ⟨1663392938487954050, 1663428406516809564⟩, true⟩

def state01 : KState := ⟨⟨360587399250096373, 360587401772526766⟩, ⟨(-130233915967012031), (-130198395465569431)⟩, true⟩

def words00 : List Nat := [360581170152572539, 360581165733680518, 360581162492797143, 360581160843889004, 360581159195114380, 360581155677806218, 360581150771093328, 360581148162230121, 360581145553536272, 360581145542866223]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574105381889711, 360574107906869796⟩, ⟨146282340187605440, 146317913760890164⟩, true⟩

def words01 : List Nat := [360581145543108468, 360581144039583916, 360581142536151937, 360581142043362347, 360581142043586654, 360581141117154452, 360581140190784357, 360581138048262740, 360581136001755101, 360581135664495199]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547971366201096, 360547973893701598⟩, ⟨690465190853234154, 690500816914061788⟩, true⟩

def words02 : List Nat := [360581136498817161, 360581136545594550, 360581136545834478, 360581134826269272, 360581133106829752, 360581129321380543, 360581127061775065, 360581126248831400, 360581125435936453, 360581123236808371]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602681794214443, 360602684324245585⟩, ⟨(-449330391550307026), (-449294712763653978)⟩, true⟩

def words03 : List Nat := [360581121645678471, 360581121302551550, 360581122253555715, 360581123248356297, 360581123248605301, 360581122304207087, 360581121940516459, 360581124041930934, 360581125076714867, 360581126111455237]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360619462091341470, 360619464623922724⟩, ⟨(-799563655562592490), (-799527923618927354)⟩, true⟩

def words04 : List Nat := [360581126111693846, 360581125997174652, 360581125376905632, 360581125565725722, 360581125565951536, 360581124202728022, 360581122930982668, 360581120511591389, 360581118092381027, 360581119799999703]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208A
