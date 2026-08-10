import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546993559173856, 360547003829279037⟩, ⟨1447443585337072389, 1447726781564171443⟩, true⟩

def state01 : KState := ⟨⟨360549454951574812, 360549465226902689⟩, ⟨1346965967828205257, 1347249377167051139⟩, true⟩

def words00 : List Nat := [360582486459602684, 360582486189672440, 360582485647909720, 360582484558262656, 360582483468578749, 360582482225600762, 360582481287057181, 360582480303819288, 360582479320569319, 360582477953615923]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569259182097897, 360569269462648561⟩, ⟨538622569234223756, 538906191741376156⟩, true⟩

def words01 : List Nat := [360582477145146812, 360582476683121290, 360582476357161823, 360582476357715821, 360582475896574766, 360582474919636825, 360582473942649905, 360582472720694261, 360582471799017088, 360582471476165009]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360550187101470133, 360550197387294312⟩, ⟨1316983003931423461, 1317266841729584147⟩, true⟩

def words02 : List Nat := [360582471153249610, 360582470374519691, 360582468998084859, 360582468220480703, 360582467442752548, 360582466292781419, 360582464728456846, 360582462825091123, 360582460921712558, 360582459617069713]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360516518152446397, 360516528443496546⟩, ⟨2691791925775138202, 2692075976976151540⟩, true⟩

def words03 : List Nat := [360582458827386036, 360582457819495683, 360582456811596988, 360582455412007060, 360582453818790625, 360582452072618692, 360582450326369757, 360582448999384722, 360582447686219152, 360582446072707520]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581722023214018, 360581732319496281⟩, ⟨28456448393506434, 28740713299688296⟩, true⟩

def words04 : List Nat := [360582444459149552, 360582443443924111, 360582442732079966, 360582441914177080, 360582441096279868, 360582439713126860, 360582438158370555, 360582437201803106, 360582436245119036, 360582435886529322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408A
