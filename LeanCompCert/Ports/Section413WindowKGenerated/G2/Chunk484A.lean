import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360498013449011378, 360498028105884715⟩, ⟨4077843104778074355, 4078322464001404067⟩, true⟩

def state01 : KState := ⟨⟨360545269101050521, 360545283764200330⟩, ⟨1790388892816084229, 1790868555852900017⟩, true⟩

def words00 : List Nat := [360582289226317945, 360582287719494828, 360582286427391116, 360582285442758708, 360582284458125502, 360582283075110480, 360582281265145501, 360582279880782243, 360582278496280882, 360582277537302022]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525225963218597, 360525240632728816⟩, ⟨2760821409975052145, 2761301380950104695⟩, true⟩

def words01 : List Nat := [360582276773745065, 360582275665785272, 360582274557727304, 360582273875171914, 360582273408191376, 360582272707334734, 360582272006432342, 360582271093531171, 360582269925853903, 360582268748816179]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549544625262463, 360549559301046072⟩, ⟨1583177570194360451, 1583657844958340737⟩, true⟩

def words02 : List Nat := [360582267571599314, 360582266644392406, 360582265811283448, 360582264766310782, 360582263721275753, 360582262419717982, 360582261443706811, 360582260780030239, 360582260116313671, 360582259235899641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557845963729096, 360557860645815304⟩, ⟨1180946290534512518, 1181426870563119854⟩, true⟩

def words03 : List Nat := [360582258561253572, 360582258072455214, 360582257583496403, 360582256711888143, 360582255557418830, 360582254036971714, 360582252516459642, 360582251420994635, 360582250638105795, 360582250135298441]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360545744650726640, 360545759339157695⟩, ⟨1767009814079351041, 1767490701483014161⟩, true⟩

def words04 : List Nat := [360582249632403803, 360582248866508841, 360582247819638933, 360582247109464460, 360582246399137827, 360582245582611429, 360582244339870777, 360582242770140028, 360582241200346321, 360582240055390575]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484A
