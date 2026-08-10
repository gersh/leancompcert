import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360665608949230890, 360665613884479326⟩, ⟨(-2385103940183948340), (-2385008143300395944)⟩, true⟩

def state01 : KState := ⟨⟨360651634649436014, 360651639588297332⟩, ⟨(-1984204160900041499), (-1984108260309457045)⟩, true⟩

def words00 : List Nat := [360582517737597142, 360582519167223011, 360582521807416820, 360582524447539990, 360582526779340746, 360582528408888195, 360582529091180760, 360582529773461416, 360582530975517215, 360582533382999382]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615744355953002, 360615749298381367⟩, ⟨(-953386898241501602), (-953290895222649158)⟩, true⟩

def words01 : List Nat := [360582537000236161, 360582540617293678, 360582543365544095, 360582546173648363, 360582548673990088, 360582551174257877, 360582553789737816, 360582555561959956, 360582556718071723, 360582557874154403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360674397100104804, 360674402046120716⟩, ⟨(-2638420484042033311), (-2638324377971485347)⟩, true⟩

def words02 : List Nat := [360582558378628319, 360582559492979802, 360582561816327998, 360582564139587076, 360582565422083142, 360582565938748301, 360582567009091752, 360582568079483440, 360582570358361189, 360582573555014542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360631410156798573, 360631415106422854⟩, ⟨(-1403143423082198988), (-1403047213324969330)⟩, true⟩

def words03 : List Nat := [360582575988490746, 360582578421841419, 360582581647354957, 360582585481425448, 360582588466000800, 360582591450424853, 360582593718944767, 360582594784401100, 360582596483397388, 360582598182400553]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611975674642840, 360611980627848678⟩, ⟨(-844451184545015056), (-844354871835971470)⟩, true⟩

def words04 : List Nat := [360582600577345685, 360582603015518256, 360582604387025966, 360582605758475852, 360582606823295378, 360582608497420841, 360582609930562259, 360582611363675046, 360582611762347448, 360582612784231553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287A
