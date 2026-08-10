import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565477867587580, 360565498093633902⟩, ⟨916527291817407522, 917299379804958236⟩, true⟩

def state01 : KState := ⟨⟨360613656239021998, 360613676472493426⟩, ⟨(-1805744090520754256), (-1804971582977477154)⟩, true⟩

def words00 : List Nat := [360581733219633074, 360581733437185156, 360581733967272491, 360581734497505512, 360581734762003465, 360581734893300303, 360581735066289997, 360581735239502448, 360581735725209439, 360581736291237079]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360628959219346374, 360628979460330753⟩, ⟨(-2670704134632048910), (-2669931202495505028)⟩, true⟩

def words01 : List Nat := [360581736590389034, 360581736889592535, 360581737376973825, 360581738021206409, 360581738533473996, 360581739045852013, 360581739401133191, 360581739925135872, 360581740761574462, 360581741598253021]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360617318626803139, 360617338875198211⟩, ⟨(-2012749514608285244), (-2011976163581864514)⟩, true⟩

def words02 : List Nat := [360581742601646175, 360581743400020617, 360581744017116909, 360581744634281086, 360581744958137161, 360581745438677120, 360581746231513518, 360581747024472727, 360581747574832852, 360581748205236918]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360638736330650124, 360638756586488427⟩, ⟨(-3223518418369704323), (-3222744646540713865)⟩, true⟩

def words03 : List Nat := [360581749147951474, 360581750090878669, 360581751346026706, 360581752459107151, 360581753306961854, 360581754154848490, 360581755095420841, 360581756202159420, 360581757210950073, 360581758219877637]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360652082608313745, 360652102871648814⟩, ⟨(-3978320049119470617), (-3977545853387886103)⟩, true⟩

def words04 : List Nat := [360581759049061422, 360581759773145827, 360581760809466491, 360581761845983999, 360581762742885719, 360581763658624497, 360581764377978846, 360581765097387232, 360581766074044541, 360581767318725119]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565A
