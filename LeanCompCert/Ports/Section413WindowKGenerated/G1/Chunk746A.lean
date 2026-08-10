import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496868855694656, 362496951857359057⟩, ⟨(-877148009884410342), (-872966499878370046)⟩, true⟩

def state01 : KState := ⟨⟨362498592901051080, 362498675925874458⟩, ⟨(-1005811887535498987), (-1001628649748382529)⟩, true⟩

def words00 : List Nat := [371285250207561366, 371285250210144748, 371285250352541598, 371285250502217176, 371285250687454760, 371285250738453044, 371285250787251077, 371285250836939198, 371285251064995361, 371285251247881289]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482146081205903, 362482229129143432⟩, ⟨221428472543758687, 225613434994160429⟩, true⟩

def words01 : List Nat := [371285251608990866, 371285251971116044, 371285252254741428, 371285252299626474, 371285252398657425, 371285252498977857, 371285252700226204, 371285252702792743, 371285252664929229, 371285252627334188]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490632722882091, 362490715793780960⟩, ⟨(-411837892040578306), (-407651216098770348)⟩, true⟩

def words02 : List Nat := [371285252705336277, 371285252735172974, 371285252943305319, 371285253152533746, 371285253340433424, 371285253343000284, 371285253310917195, 371285253333478716, 371285253494237198, 371285253570092429]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487674730567285, 362487757824870909⟩, ⟨(-191054565895997460), (-186866143138406528)⟩, true⟩

def words03 : List Nat := [371285253645408446, 371285253721618583, 371285253915416451, 371285254045442911, 371285254142837461, 371285254241175462, 371285254337997581, 371285254340565370, 371285254255964200, 371285254292721844]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475860425456395, 362475943542663905⟩, ⟨690823823486430233, 695013955905969969⟩, true⟩

def words04 : List Nat := [371285254403138961, 371285254405706445, 371285254277139450, 371285254148881164, 371285254019665962, 371285253946486839, 371285253842443221, 371285253849355123, 371285253851274432, 371285253843479793]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk746A
