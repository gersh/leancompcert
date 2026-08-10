import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598043332315533, 360598059015749787⟩, ⟨(-807977783359174908), (-807447912580767286)⟩, true⟩

def state01 : KState := ⟨⟨360592294546560302, 360592310236573243⟩, ⟨(-520683991827620725), (-520153792082174189)⟩, true⟩

def words00 : List Nat := [360581910395442738, 360581910396133774, 360581910304120897, 360581910379766878, 360581910380344477, 360581910285172222, 360581910131978940, 360581909750752259, 360581909369395282, 360581909448904887]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546267369295873, 360546283065802535⟩, ⟨1781439420340147163, 1781969944870095949⟩, true⟩

def words01 : List Nat := [360581909775615383, 360581910102442398, 360581910228141910, 360581910228834009, 360581910226192367, 360581909943203974, 360581909660028326, 360581909438014455, 360581908926157786, 360581908214640402]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575472756386833, 360575488459421143⟩, ⟨320586621109944638, 321117472184346964⟩, true⟩

def words02 : List Nat := [360581907502994687, 360581907190346645, 360581907589508250, 360581907988853368, 360581908001115818, 360581908001806191, 360581907615447885, 360581907401563992, 360581907187491016, 360581906957765824]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563489798441348, 360563505508053921⟩, ⟨920207775586759713, 920738955803902261⟩, true⟩

def words03 : List Nat := [360581906830098303, 360581906427012883, 360581906023811064, 360581906242911179, 360581906367133659, 360581906491475781, 360581906492093689, 360581906362338768, 360581905934042502, 360581905567122744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583604570473726, 360583620286601208⟩, ⟨(-86551635908759366), (-86020129654183364)⟩, true⟩

def words04 : List Nat := [360581905199981380, 360581905137991659, 360581904786387065, 360581904127275194, 360581903468077011, 360581902709359662, 360581902195337124, 360581902079799933, 360581901964194909, 360581901637030687]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500A
