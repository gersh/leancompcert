import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360520110231390120, 360520112294284892⟩, ⟨1236892726155368827, 1236919115059142493⟩, true⟩

def state01 : KState := ⟨⟨360484879725396091, 360484881790561179⟩, ⟨1902985829984807055, 1903012261808840553⟩, true⟩

def words00 : List Nat := [360585554287763983, 360585552410940537, 360585549782702988, 360585545754694939, 360585541727073537, 360585536367727031, 360585532857249025, 360585528299231046, 360585523741671938, 360585517023866777]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360677622846420316, 360677624913862021⟩, ⟨(-1742825194860687696), (-1742798719974383456)⟩, true⟩

def words01 : List Nat := [360585511702543676, 360585509164074205, 360585506869532458, 360585507339123941, 360585507339347328, 360585505251989777, 360585503858526454, 360585505947297852, 360585510816360350, 360585515684964269]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587922242383469, 360587924312126773⟩, ⟨(-45728246126195328), (-45701727682284478)⟩, true⟩

def words02 : List Nat := [360585518039891487, 360585518040133024, 360585519098980095, 360585520584471718, 360585521309778700, 360585521310020262, 360585519254661307, 360585515778851327, 360585512303357608, 360585510190966651]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360458875482858827, 360458877554875105⟩, ⟨2397820859725825601, 2397847421208921675⟩, true⟩

def words03 : List Nat := [360585510734804406, 360585511278629570, 360585511278844785, 360585510429241559, 360585506800479992, 360585501201427765, 360585495602894260, 360585491471148603, 360585486531931584, 360585479847441574]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360495160243527509, 360495162317829463⟩, ⟨1710458512933116801, 1710485117718143125⟩, true⟩

def words04 : List Nat := [360585473163604112, 360585466084430473, 360585461826952053, 360585458736824638, 360585455647006294, 360585450166417345, 360585441910979667, 360585436428034829, 360585430945601532, 360585425384727519]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189A
