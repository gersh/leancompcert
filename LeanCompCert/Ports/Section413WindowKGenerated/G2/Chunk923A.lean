import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589383297699708, 360589439406530821⟩, ⟨(-691900529032398054), (-688403419545821562)⟩, true⟩

def state01 : KState := ⟨⟨360584186639380743, 360584242760937962⟩, ⟨(-212252978460797496), (-208754694292194458)⟩, true⟩

def words00 : List Nat := [360581981163293706, 360581981193733258, 360581981328652792, 360581981463975371, 360581981569605064, 360581981570940081, 360581981559550040, 360581981476657257, 360581981393528794, 360581981332784306]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573925616902828, 360573981751028850⟩, ⟨735033080582340280, 738532525039851804⟩, true⟩

def words01 : List Nat := [360581981475564560, 360581981618606766, 360581981686234199, 360581981687569434, 360581981669161784, 360581981595653711, 360581981563919387, 360581981565255619, 360581981538693652, 360581981453423130]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587678337524572, 360587734484276055⟩, ⟨(-534753611426846464), (-531253001325527056)⟩, true⟩

def words02 : List Nat := [360581981367854267, 360581981297708127, 360581981298813835, 360581981239530748, 360581981180146609, 360581981020741329, 360581980870764953, 360581980760891804, 360581980650628838, 360581980696259836]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583358162643973, 360583414322120915⟩, ⟨(-135814767437926550), (-132312982334063450)⟩, true⟩

def words03 : List Nat := [360581980701440340, 360581980706755902, 360581980828965016, 360581981042154327, 360581981202504318, 360581981363069803, 360581981433236291, 360581981434571835, 360581981431447388, 360581981448507525]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579059496983662, 360579115669028797⟩, ⟨261119810510122029, 264622756224524319⟩, true⟩

def words04 : List Nat := [360581981559050925, 360581981560386468, 360581981554039397, 360581981488991370, 360581981423709183, 360581981256134759, 360581981153372838, 360581981161344991, 360581981162546995, 360581981102231012]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923A
