import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484578664732908, 362484634417090625⟩, ⟨41692488899436105, 44012260318692195⟩, true⟩

def state01 : KState := ⟨⟨362492802700933596, 362492858471951901⟩, ⟨(-464891475348574185), (-462570554340640219)⟩, true⟩

def words00 : List Nat := [371285349110627542, 371285349200538990, 371285349553307261, 371285349906894760, 371285350197804409, 371285350199893608, 371285350145845107, 371285350154815660, 371285350426381151, 371285350550406388]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494502287006799, 362494558077044862⟩, ⟨(-569581635495832470), (-567259542585697464)⟩, true⟩

def words01 : List Nat := [371285350623879619, 371285350698026561, 371285351035018399, 371285351280265160, 371285351603810296, 371285351928172151, 371285352216237695, 371285352218327337, 371285352304546318, 371285352456516379]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482515165713018, 362482570974372746⟩, ⟨169130156658208286, 171453397133456716⟩, true⟩

def words02 : List Nat := [371285352715734876, 371285352740000602, 371285352741578216, 371285352734342243, 371285352726294980, 371285352719213080, 371285352702886354, 371285352828073629, 371285352951718128, 371285352953881646]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499334870828190, 362499390698396357⟩, ⟨(-867564462548855501), (-865240056652636669)⟩, true⟩

def words03 : List Nat := [371285353128537270, 371285353349462699, 371285353645954513, 371285353648044811, 371285353593833772, 371285353466450374, 371285353472074902, 371285353476990755, 371285353706138230, 371285353936230711]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498080296396177, 362498136142871224⟩, ⟨(-790213625555821509), (-787888054143049937)⟩, true⟩

def words04 : List Nat := [371285354165615425, 371285354242937599, 371285354582963086, 371285354924054682, 371285355343272420, 371285355512071201, 371285355679527030, 371285355847710667, 371285356123362734, 371285356333068577]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616A
