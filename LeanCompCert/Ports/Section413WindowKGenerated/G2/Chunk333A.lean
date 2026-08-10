import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557802214795053, 360557808943249913⟩, ⟨781758214704892606, 781909710241418054⟩, true⟩

def state01 : KState := ⟨⟨360560582918916043, 360560589651560445⟩, ⟨689104694897799699, 689256329967195839⟩, true⟩

def words00 : List Nat := [360581289205007674, 360581289205452460, 360581288501229638, 360581287174266961, 360581285847310900, 360581284291734422, 360581283492539569, 360581283087900516, 360581282683237984, 360581281825981556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568777466879409, 360568784203728987⟩, ⟨416127907074417417, 416279682239409021⟩, true⟩

def words01 : List Nat := [360581281482962387, 360581281761238109, 360581282014150980, 360581282014595950, 360581281369197863, 360581279953991320, 360581278538784703, 360581278022461462, 360581277966044391, 360581277591551299]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547798718975603, 360547805460060877⟩, ⟨1114906852392274316, 1115058768711193822⟩, true⟩

def words02 : List Nat := [360581277217007865, 360581276278458806, 360581274441864391, 360581273203679507, 360581271965452156, 360581270247141584, 360581268155630582, 360581265327100716, 360581262498655536, 360581260568633071]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360506008832706548, 360506015577981281⟩, ⟨2508185808483770821, 2508337864458624581⟩, true⟩

def words03 : List Nat := [360581259565269649, 360581259460102271, 360581259354890779, 360581258677062555, 360581258026373672, 360581256973169680, 360581255919895389, 360581254728081408, 360581252923105413, 360581250666897257]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560908691110306, 360560915440595663⟩, ⟨677339102825801977, 677491299203013161⟩, true⟩

def words04 : List Nat := [360581248410732500, 360581245675970709, 360581243393588818, 360581242009019923, 360581240624506241, 360581238502971577, 360581235485091442, 360581233364960542, 360581231244818135, 360581230022280911]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333A
