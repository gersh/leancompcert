import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583569322316901, 360583622934365086⟩, ⟨(-150304951415405698), (-147035808044776816)⟩, true⟩

def state01 : KState := ⟨⟨360578105633338636, 360578159257652494⟩, ⟨343076078173695417, 346346329196100791⟩, true⟩

def words00 : List Nat := [360581994760041301, 360581994777166980, 360581994778329008, 360581994726266469, 360581994673988694, 360581994591285427, 360581994585250748, 360581994524196079, 360581994463000505, 360581994340469415]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604185498616994, 360604239135218408⟩, ⟨(-2012359461674427729), (-2009088100901475503)⟩, true⟩

def words01 : List Nat := [360581994299062675, 360581994294654486, 360581994406522280, 360581994527535824, 360581994538105707, 360581994548764376, 360581994631179424, 360581994775582649, 360581995022920096, 360581995270547939]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591965916861486, 360592019565901303⟩, ⟨(-908753196005602593), (-905480711735490269)⟩, true⟩

def words02 : List Nat := [360581995392399281, 360581995393703010, 360581995463666060, 360581995535811409, 360581995576095150, 360581995577401719, 360581995564462458, 360581995490186903, 360581995422802632, 360581995535261374]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575564345515752, 360575618006826579⟩, ⟨572926984650581659, 576200577423904605⟩, true⟩

def words03 : List Nat := [360581995741371941, 360581995947736750, 360581996092842536, 360581996192633111, 360581996193744316, 360581996189620484, 360581996216203270, 360581996217510801, 360581996209546021, 360581996140293747]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587625868589971, 360587679542231979⟩, ⟨(-516759138516506488), (-513484431685490028)⟩, true⟩

def words04 : List Nat := [360581996086265087, 360581996200644437, 360581996294970012, 360581996389537823, 360581996390743205, 360581996383980540, 360581996279909026, 360581996274817782, 360581996269361903, 360581996324207990]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk903A
