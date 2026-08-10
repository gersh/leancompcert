import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk643A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572767593078541, 360572794060538156⟩, ⟨647949167569213758, 649098801304266406⟩, true⟩

def state01 : KState := ⟨⟨360625271172673328, 360625297648680199⟩, ⟨(-2728226599455506937), (-2727076416089312657)⟩, true⟩

def words00 : List Nat := [360582888838054369, 360582889111217599, 360582889625684416, 360582890140308422, 360582890445206013, 360582890814150501, 360582891371032653, 360582891928164192, 360582892478779157, 360582893139092581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360613083907438985, 360613110392063501⟩, ⟨(-1944415136038505887), (-1943264398428700453)⟩, true⟩

def words01 : List Nat := [360582893600979479, 360582894062944678, 360582894703153822, 360582895468974463, 360582896123208998, 360582896777584864, 360582897247392152, 360582897476565773, 360582897947025806, 360582898417771611]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624070937440096, 360624097430602774⟩, ⟨(-2651211831831852655), (-2650060545005807571)⟩, true⟩

def words02 : List Nat := [360582899080274327, 360582899612348454, 360582899957268621, 360582900302259403, 360582900537504859, 360582900921234300, 360582901546093040, 360582902171114514, 360582902644246076, 360582903285555973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360629314597815623, 360629341099517678⟩, ⟨(-2988526758259992890), (-2987374922051957980)⟩, true⟩

def words03 : List Nat := [360582904040798718, 360582904796291665, 360582905792853981, 360582906684254310, 360582907371278732, 360582908058352272, 360582908622787708, 360582909308072965, 360582910030472852, 360582910753050388]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610506414966825, 360610532925302025⟩, ⟨(-1778459260774918842), (-1777306869070235330)⟩, true⟩

def words04 : List Nat := [360582911354082736, 360582911794516373, 360582912315646583, 360582912837042773, 360582913214195492, 360582913350996934, 360582913351803733, 360582913352293982, 360582913547881986, 360582913978136166]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk643A
