import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567514605738292, 360567521503625384⟩, ⟨461691081107534139, 461848252694324225⟩, true⟩

def state01 : KState := ⟨⟨360629699127149442, 360629706029287494⟩, ⟨(-1634132100589005259), (-1633974785723679491)⟩, true⟩

def words00 : List Nat := [360581225996486975, 360581226775442380, 360581228433288452, 360581230091125338, 360581230925302497, 360581231388362981, 360581232346023027, 360581233303758062, 360581234513373961, 360581235951694908]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605399906247845, 360605406812681363⟩, ⟨(-814818367735458790), (-814660908048240742)⟩, true⟩

def words01 : List Nat := [360581236788481884, 360581237625275440, 360581239340462510, 360581241498907024, 360581243072856471, 360581244646783607, 360581245777809952, 360581246519141231, 360581247236009579, 360581247952978263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360631152525368132, 360631159436048997⟩, ⟨(-1683300069891984104), (-1683142466962919626)⟩, true⟩

def words02 : List Nat := [360581249547883120, 360581250893197286, 360581251792175443, 360581252691145455, 360581253105709086, 360581254335691957, 360581256030281796, 360581257724858656, 360581258977030214, 360581260456861813]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360648580266920778, 360648587181862917⟩, ⟨(-2271346644242203194), (-2271188897558764736)⟩, true⟩

def words03 : List Nat := [360581262573562567, 360581264690274350, 360581266571335895, 360581267870061754, 360581268415116297, 360581268960171979, 360581269636354814, 360581270755001023, 360581272750517866, 360581274746026435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611255053574891, 360611261972818573⟩, ⟨(-1012123029574738592), (-1011965137736661148)⟩, true⟩

def words04 : List Nat := [360581276141825020, 360581276663193178, 360581277685884770, 360581278708648937, 360581279205232303, 360581279205683741, 360581279145257836, 360581278411458971, 360581277820069229, 360581278708982342]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337A
