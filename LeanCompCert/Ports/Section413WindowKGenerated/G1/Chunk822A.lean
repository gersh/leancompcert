import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494093054999594, 362494194586231169⟩, ⟨(-741448620938037987), (-735813170621042191)⟩, true⟩

def state01 : KState := ⟨⟨362482599304645437, 362482700861267830⟩, ⟨203393168567750567, 209030706143631929⟩, true⟩

def words00 : List Nat := [371285243368342237, 371285243381276178, 371285243383420912, 371285243366261968, 371285243349219352, 371285243352387426, 371285243357306893, 371285243436003724, 371285243501624874, 371285243504573312]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508520995427687, 362508622577756967⟩, ⟨(-1927765327413526710), (-1922125676347663398)⟩, true⟩

def words01 : List Nat := [371285243575408002, 371285243678642502, 371285243889317578, 371285243989284026, 371285244047628129, 371285244106820436, 371285244312825131, 371285244452309952, 371285244738578182, 371285245026081025]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491905168916969, 362492006776982708⟩, ⟨(-561514655599209021), (-555872888349953993)⟩, true⟩

def words02 : List Nat := [371285245312393475, 371285245476690293, 371285245787996913, 371285246100844305, 371285246391911451, 371285246486631589, 371285246580500821, 371285246675304620, 371285246796980152, 371285246882437465]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491756084222594, 362491857717974374⟩, ⟨(-549212486934274345), (-543568607392497769)⟩, true⟩

def words03 : List Nat := [371285247114526984, 371285247347802672, 371285247579779710, 371285247615326360, 371285247695303998, 371285247776740533, 371285248004574889, 371285248091771226, 371285248174271285, 371285248257882784]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362502833359344260, 362502935018628448⟩, ⟨(-1460250482474046359), (-1454604503018292573)⟩, true⟩

def words04 : List Nat := [371285248488104006, 371285248645859506, 371285248854714952, 371285249064666833, 371285249249761883, 371285249311637424, 371285249447821165, 371285249585496932, 371285249854491312, 371285250072512069]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822A
