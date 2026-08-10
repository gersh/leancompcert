import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538110800179808, 360538124103813003⟩, ⟨2078324369899577186, 2078739708439752594⟩, true⟩

def state01 : KState := ⟨⟨360527841795645378, 360527855105241414⟩, ⟨2552848600002795986, 2553264214056563396⟩, true⟩

def words00 : List Nat := [360583117496426187, 360583116836928988, 360583116041347090, 360583115011913977, 360583113982422111, 360583112834782066, 360583112025600195, 360583110972813710, 360583109920002332, 360583108604788191]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575371179052537, 360575384494626854⟩, ⟨356163504147217660, 356579394487663680⟩, true⟩

def words01 : List Nat := [360583107409625663, 360583106286836303, 360583105163910177, 360583104309820118, 360583103472979505, 360583102232100953, 360583100991154633, 360583100123247756, 360583099489848776, 360583099323585913]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573091649534896, 360573104971159377⟩, ⟨461322522859101958, 461738692866336788⟩, true⟩

def words02 : List Nat := [360583099157249178, 360583098617429166, 360583098043218777, 360583097628065479, 360583097212756076, 360583096609554669, 360583095764883000, 360583094630816888, 360583093496664501, 360583092829538489]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360533152807904610, 360533166135493404⟩, ⟨2307948298474091065, 2308364744242440829⟩, true⟩

def words03 : List Nat := [360583092745815447, 360583092878250512, 360583092878824513, 360583092664017278, 360583091982193640, 360583090980262384, 360583089978188670, 360583089442899377, 360583088597350427, 360583087518370620]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570920396545742, 360570933730131184⟩, ⟨561424903926370564, 561841627008993970⟩, true⟩

def words04 : List Nat := [360583086439294581, 360583085497792086, 360583084921477758, 360583084702977286, 360583084484432575, 360583083867782538, 360583083054213983, 360583082592332027, 360583082130292593, 360583081657201649]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462A
