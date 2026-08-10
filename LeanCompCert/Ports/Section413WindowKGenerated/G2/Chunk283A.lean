import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575095219557545, 360575100012429469⟩, ⟨204404955134159009, 204496694221785591⟩, true⟩

def state01 : KState := ⟨⟨360591801811472631, 360591806607873696⟩, ⟨(-268756937210422233), (-268665098231231679)⟩, true⟩

def words00 : List Nat := [360582325789008217, 360582324987288667, 360582324932739786, 360582324653728757, 360582324374712118, 360582322796833117, 360582319976999902, 360582318401571171, 360582316826137610, 360582316830111299]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577201500920832, 360577206300875982⟩, ⟨144641415387075571, 144733355000074429⟩, true⟩

def words01 : List Nat := [360582316830444004, 360582316542478265, 360582316534732647, 360582317845000845, 360582318285980057, 360582318726983682, 360582318727316481, 360582318545307653, 360582317121983590, 360582316941942369]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580771061281596, 360580775864759681⟩, ⟨43676692724580883, 43768732124684999⟩, true⟩

def words02 : List Nat := [360582317464718916, 360582318677188240, 360582319263708485, 360582319850224782, 360582319850539908, 360582319849284450, 360582320521570442, 360582321193878976, 360582321194218353, 360582320825300616]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360621445008923207, 360621449815929574⟩, ⟨(-1108865985053106521), (-1108773845679061431)⟩, true⟩

def words03 : List Nat := [360582321439330398, 360582322107958378, 360582323429653754, 360582324042525244, 360582324042869816, 360582323596731666, 360582323484835033, 360582324445758242, 360582325826632040, 360582327207493773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576389811906048, 360576394622479996⟩, ⟨167855595674150037, 167947836170329733⟩, true⟩

def words04 : List Nat := [360582327783978979, 360582327784353037, 360582327696049255, 360582327576447300, 360582327456755049, 360582327020058073, 360582325345122070, 360582322719395987, 360582320093782960, 360582318708411931]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283A
