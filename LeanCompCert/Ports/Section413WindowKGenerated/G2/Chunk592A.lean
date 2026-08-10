import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360544386343956401, 360544408632406384⟩, ⟨2225751454422157330, 2226642875568567246⟩, true⟩

def state01 : KState := ⟨⟨360611104699414866, 360611126995675635⟩, ⟨(-1724331644089870952), (-1723439760507741974)⟩, true⟩

def words00 : List Nat := [360582020208480615, 360582019772333621, 360582019619227590, 360582019647670808, 360582019648433621, 360582019435843519, 360582019308838967, 360582019388597334, 360582019753465513, 360582020245907725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589852526534185, 360589874830694027⟩, ⟨(-465966847656826695), (-465074496333790769)⟩, true⟩

def words01 : List Nat := [360582020522494020, 360582020799151648, 360582020928626374, 360582021228544438, 360582021371310848, 360582021514204409, 360582021514941546, 360582021514147066, 360582021494764604, 360582021628344628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573438082693472, 360573460394644276⟩, ⟨506180054965024698, 507072867708637700⟩, true⟩

def words02 : List Nat := [360582022046886724, 360582022181345005, 360582022182083773, 360582022145579217, 360582022108936949, 360582021902399812, 360582021837398805, 360582021764487772, 360582021691489262, 360582021476320938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620525202721665, 360620547522478919⟩, ⟨(-2283056931163354237), (-2282163656004022941)⟩, true⟩

def words03 : List Nat := [360582021386246700, 360582021440950702, 360582021780559851, 360582022127091323, 360582022187365497, 360582022247697439, 360582022472469541, 360582022838631862, 360582023489616468, 360582024140766862]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618349502315832, 360618371829970753⟩, ⟨(-2154300708197139516), (-2153406965142655038)⟩, true⟩

def words04 : List Nat := [360582024566036698, 360582024868281762, 360582025455414220, 360582026042769906, 360582026417468302, 360582026749964666, 360582026894179735, 360582027038488564, 360582027407672679, 360582028022015737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592A
