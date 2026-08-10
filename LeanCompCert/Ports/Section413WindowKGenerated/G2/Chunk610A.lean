import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566222224590070, 360566245945322044⟩, ⟨988348153434809820, 989325661531329580⟩, true⟩

def state01 : KState := ⟨⟨360610417120069627, 360610440848863728⟩, ⟨(-1707700479366843921), (-1706722479441249443)⟩, true⟩

def words00 : List Nat := [360582464136466217, 360582464277378772, 360582464602607826, 360582464927990011, 360582465007918657, 360582465154643523, 360582465569861814, 360582465985318478, 360582466376918052, 360582466836317774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568449068820104, 360568472805766505⟩, ⟨853048141795349515, 854026639132462635⟩, true⟩

def words01 : List Nat := [360582467161145853, 360582467486064576, 360582467771691495, 360582468191264618, 360582468541866640, 360582468892597593, 360582469020680994, 360582469021535652, 360582468882055037, 360582468653671003]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595444651314141, 360595468396309009⟩, ⟨(-794399173179106682), (-793420184684196742)⟩, true⟩

def words02 : List Nat := [360582468425000670, 360582468410966751, 360582468318750976, 360582468091625242, 360582467864368146, 360582467569863230, 360582467667790264, 360582467851513098, 360582467900834210, 360582468114735970]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598575102917783, 360598598855988294⟩, ⟨(-985457806991813605), (-984478325599514921)⟩, true⟩

def words03 : List Nat := [360582468596901771, 360582469079302751, 360582469553799742, 360582469761049630, 360582469761841396, 360582469737384502, 360582469876127037, 360582470177224623, 360582470442152135, 360582470707275142]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591310292224215, 360591334053437184⟩, ⟨(-542084073791922170), (-541104095346299920)⟩, true⟩

def words04 : List Nat := [360582470837343797, 360582470842546238, 360582471115933655, 360582471389563132, 360582471538159632, 360582471539014781, 360582471487822508, 360582471192570717, 360582470897160881, 360582470904670640]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610A
