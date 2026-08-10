import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488301922867332, 362488433423399354⟩, ⟨(-315595230456967101), (-307329317090747761)⟩, true⟩

def state01 : KState := ⟨⟨362495004409547822, 362495135939215521⟩, ⟨(-939578394852436932), (-931309768804386448)⟩, true⟩

def words00 : List Nat := [371285132531741391, 371285132618830828, 371285132819916786, 371285133022397413, 371285133204394056, 371285133276682560, 371285133387361615, 371285133499653853, 371285133682928716, 371285133793724609]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490835411093638, 362490966970477052⟩, ⟨(-551342268125697033), (-543070875101265283)⟩, true⟩

def words01 : List Nat := [371285133893887061, 371285133995176729, 371285134210470779, 371285134386382472, 371285134566521266, 371285134747859773, 371285134927804398, 371285134954850838, 371285135019706646, 371285135086421885]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481362573918768, 362481494162347586⟩, ⟨330807072690196760, 339081170571375880⟩, true⟩

def words02 : List Nat := [371285135187083595, 371285135190342188, 371285135148458204, 371285135106274072, 371285135062871824, 371285135049267532, 371285135038351283, 371285135076820839, 371285135103572841, 371285135106947301]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498396904374914, 362498528522215053⟩, ⟨(-1255680663507056047), (-1247403826400279253)⟩, true⟩

def words03 : List Nat := [371285135146289971, 371285135226436240, 371285135420189853, 371285135461319545, 371285135473483863, 371285135486661916, 371285135557296097, 371285135589389676, 371285135735393114, 371285135882814572]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485131674788965, 362485263322097762⟩, ⟨(-20097852575716032), (-11818270611828780)⟩, true⟩

def words04 : List Nat := [371285136027299619, 371285136076750191, 371285136197694542, 371285136320350364, 371285136461630873, 371285136464890225, 371285136452676728, 371285136435855173, 371285136444786400, 371285136449915909]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931A
