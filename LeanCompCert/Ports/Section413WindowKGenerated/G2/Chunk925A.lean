import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569511015436892, 360569567377267072⟩, ⟨1146006761397226850, 1149527247986286202⟩, true⟩

def state01 : KState := ⟨⟨360606947097528571, 360607003471987823⟩, ⟨(-2317035518233578849), (-2313513863393391611)⟩, true⟩

def words00 : List Nat := [360581994565600506, 360581994552991620, 360581994694352678, 360581994835968230, 360581994866833734, 360581994868173820, 360581994937883258, 360581995032049599, 360581995213501870, 360581995485225240]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598695497857762, 360598751885076459⟩, ⟨(-1553606539404372606), (-1550083704124706648)⟩, true⟩

def words01 : List Nat := [360581995682877170, 360581995880681065, 360581996162996097, 360581996528301600, 360581996864035002, 360581997199979636, 360581997477110748, 360581997662175878, 360581997844364096, 360581998026988839]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590297030869044, 360590353430688675⟩, ⟨(-776616970966209976), (-773092969784482462)⟩, true⟩

def words02 : List Nat := [360581998172234854, 360581998201207549, 360581998202399875, 360581998172727056, 360581998142837838, 360581998113197515, 360581998227171430, 360581998341399315, 360581998377211198, 360581998468894418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595276309669857, 360595332722145444⟩, ⟨(-1237410164963831719), (-1233884992665426315)⟩, true⟩

def words03 : List Nat := [360581998599847214, 360581998731197434, 360581998859547808, 360581998953776109, 360581998955011548, 360581998955876913, 360581998961752777, 360581999044200306, 360581999189368856, 360581999334861263]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568265483649864, 360568321908868448⟩, ⟨1262211799132119794, 1265738150730522680⟩, true⟩

def words04 : List Nat := [360581999420952147, 360581999422290854, 360581999391805585, 360581999349737708, 360581999307315843, 360581999218205418, 360581999012522519, 360581998715361229, 360581998417948483, 360581998171977368]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925A
