import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489227119361644, 362489358326762747⟩, ⟨(-401568265251007821), (-393329627750623187)⟩, true⟩

def state01 : KState := ⟨⟨362486249509970227, 362486380746396455⟩, ⟨(-124582552763501549), (-116341215775979067)⟩, true⟩

def words00 : List Nat := [371285129184725374, 371285129287799620, 371285129382949364, 371285129479165061, 371285129570351691, 371285129604779869, 371285129710609106, 371285129817797995, 371285129896711826, 371285129913529634]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504223960012344, 362504355225803640⟩, ⟨(-1796478660519763302), (-1788234592139445776)⟩, true⟩

def words01 : List Nat := [371285130035386336, 371285130158899211, 371285130377674665, 371285130443437103, 371285130496069906, 371285130549792514, 371285130710333670, 371285130818589198, 371285131027465365, 371285131237756431]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485108100389899, 362485239395610570⟩, ⟨(-18272207604376332), (-10025401560696290)⟩, true⟩

def words02 : List Nat := [371285131439972463, 371285131488979461, 371285131566833062, 371285131646439112, 371285131752314837, 371285131755569611, 371285131717554091, 371285131659696746, 371285131626578381, 371285131631515154]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476872917961710, 362477004242473889⟩, ⟨747928163142292017, 756177694328736539⟩, true⟩

def words03 : List Nat := [371285131731867458, 371285131833573854, 371285131934786170, 371285131938041431, 371285131895642092, 371285131867792348, 371285131854737420, 371285131858014938, 371285131773400942, 371285131689747414]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475031794915020, 362475163148557963⟩, ⟨919250848009550891, 927503089673515813⟩, true⟩

def words04 : List Nat := [371285131604617917, 371285131567479919, 371285131472101947, 371285131439954263, 371285131406761367, 371285131356016805, 371285131150275608, 371285131061775484, 371285130971574174, 371285130941031618]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk930A
