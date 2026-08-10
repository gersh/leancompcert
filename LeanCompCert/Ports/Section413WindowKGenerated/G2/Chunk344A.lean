import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360628227661272318, 360628234860988283⟩, ⟨(-1605318928698573639), (-1605151479457704101)⟩, true⟩

def state01 : KState := ⟨⟨360598480647919012, 360598487852018219⟩, ⟨(-582058237874944574), (-581890637828928566)⟩, true⟩

def words00 : List Nat := [360581575768429521, 360581576124211896, 360581577323736450, 360581578523326350, 360581579140207695, 360581579140668466, 360581578915794028, 360581578269369807, 360581577622890880, 360581577833773213]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360520288645217410, 360520295853660109⟩, ⟨2109050999395682140, 2109218748923663528⟩, true⟩

def words01 : List Nat := [360581578566583574, 360581579299445768, 360581579607080513, 360581579607541399, 360581579073742554, 360581578326668780, 360581577579498915, 360581577462826436, 360581576504826730, 360581574724924597]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360623480166107526, 360623487378901916⟩, ⟨(-1443385873456984772), (-1443217974122490412)⟩, true⟩

def words02 : List Nat := [360581572945021667, 360581572008163047, 360581571495138149, 360581571429702554, 360581571364238441, 360581570485932193, 360581569630160045, 360581569447343815, 360581569923465978, 360581571141379844]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596304078014854, 360596311295202840⟩, ⟨(-507661349846960045), (-507493299219055853)⟩, true⟩

def words03 : List Nat := [360581571822577981, 360581572503786476, 360581573158406321, 360581574238379944, 360581574903629452, 360581575568915576, 360581575702307937, 360581575702769302, 360581575716874182, 360581576145258906]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556650922994080, 360556658144524226⟩, ⟨858084349380643809, 858252549573928743⟩, true⟩

def words04 : List Nat := [360581576391868272, 360581576392330846, 360581576371342319, 360581575822503344, 360581575273620909, 360581574453347124, 360581574056093813, 360581573224008037, 360581572391920131, 360581571135803586]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344A
