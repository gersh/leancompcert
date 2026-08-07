import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk565

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472377655889774, 362472424237922942⟩, ⟨702472875001472077, 704250775507076605⟩, true⟩

def state01 : KState := ⟨⟨362494780401172784, 362494827000232444⟩, ⟨(-563325221977740572), (-561546359387649326)⟩, true⟩

def words00 : List Nat := [371284888726595099, 371284888728713178, 371284888968849152, 371284889246922186, 371284889475147063, 371284889477054852, 371284889442528184, 371284889506942642, 371284889883425819, 371284890061240254]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508916102557827, 362508962719022729⟩, ⟨(-1362238834020538299), (-1360458987774508113)⟩, true⟩

def words01 : List Nat := [371284890181250456, 371284890301876888, 371284890683213965, 371284890909129198, 371284891197615916, 371284891486803876, 371284891774912053, 371284891889809895, 371284892316983517, 371284892745247062]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491796634980208, 362491843268394706⟩, ⟨(-394529732881248146), (-392748928554363146)⟩, true⟩

def words02 : List Nat := [371284893404060094, 371284893689441161, 371284893958350803, 371284894227885594, 371284894462119432, 371284894540931529, 371284894931805618, 371284895323464772, 371284895646954966, 371284895771825490]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362512682136655328, 362512728787287581⟩, ⟨(-1575220200680362480), (-1573438422945685640)⟩, true⟩

def words03 : List Nat := [371284896208856520, 371284896646876710, 371284897396709654, 371284897809575062, 371284898173188758, 371284898537400117, 371284899108170600, 371284899525750119, 371284900019270484, 371284900513593347]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513855015546627, 362513901683365222⟩, ⟨(-1641601893154888180), (-1639819143620794534)⟩, true⟩

def words04 : List Nat := [371284900991689121, 371284901151937500, 371284901624323925, 371284902097714400, 371284902638616480, 371284902922679995, 371284903180704129, 371284903439331228, 371284903995172157, 371284904510130076]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485309509711223, 362485356194719634⟩, ⟨(-27166384421134776), (-25382662714777174)⟩, true⟩

def words05 : List Nat := [371284905126546480, 371284905743723214, 371284906299593035, 371284906439264220, 371284906673226819, 371284906908122587, 371284907366575525, 371284907409060120, 371284907418423242, 371284907428560713]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488784304846096, 362488831006887100⟩, ⟨(-223667935058907525), (-221883249899700689)⟩, true⟩

def words06 : List Nat := [371284907706109319, 371284907873636656, 371284908170881534, 371284908468864493, 371284908713842013, 371284908715747734, 371284908544092778, 371284908502079373, 371284908727207266, 371284908798513558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482281460102690, 362482328179498915⟩, ⟨144253129993351301, 146038797022681997⟩, true⟩

def words07 : List Nat := [371284908867876775, 371284908937863060, 371284909112444261, 371284909175684837, 371284909316859944, 371284909458799456, 371284909599447673, 371284909601353663, 371284909325586070, 371284909282309497]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469151634657498, 362469198371044858⟩, ⟨887203692711923094, 888990321188367206⟩, true⟩

def words08 : List Nat := [371284909278754352, 371284909280664746, 371284908999168684, 371284908718869131, 371284908437819187, 371284908252378115, 371284907910405430, 371284907838639787, 371284907766220542, 371284907689319967]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494269480174712, 362494316233802406⟩, ⟨(-534352194814414753), (-532564590621126199)⟩, true⟩

def words09 : List Nat := [371284907447667088, 371284907484643575, 371284907714954350, 371284907716861062, 371284907531342162, 371284907230944470, 371284906939530484, 371284906941631429, 371284906963255650, 371284907131655428]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk565
