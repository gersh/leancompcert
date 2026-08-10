import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589233117945588, 360589284533677859⟩, ⟨(-635297867076638357), (-632225081428686273)⟩, true⟩

def state01 : KState := ⟨⟨360593555321155690, 360593606748923695⟩, ⟨(-1017875643771600496), (-1014801792905056758)⟩, true⟩

def words00 : List Nat := [360582140880318059, 360582140953086524, 360582140961799426, 360582140970659914, 360582140971727950, 360582140981501106, 360582141130303095, 360582141279369528, 360582141356201922, 360582141487059011]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592273756499627, 360592325196298425⟩, ⟨(-904402267660223034), (-901327351887155024)⟩, true⟩

def words01 : List Nat := [360582141707254550, 360582141927819693, 360582142275429786, 360582142495760895, 360582142598852731, 360582142702009652, 360582142763844985, 360582142890122999, 360582143006185663, 360582143122531894]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585484028515135, 360585535480479796⟩, ⟨(-303370614277290758), (-300294621521252102)⟩, true⟩

def words02 : List Nat := [360582143161416745, 360582143203602215, 360582143372925880, 360582143542633727, 360582143679275367, 360582143688643382, 360582143689781600, 360582143617763290, 360582143545511432, 360582143509062765]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555686269361832, 360555737733337877⟩, ⟨2334852909575601200, 2337929965759527314⟩, true⟩

def words03 : List Nat := [360582143650078909, 360582143791336466, 360582143868833520, 360582143870109339, 360582143820066873, 360582143738301654, 360582143656135466, 360582143583545235, 360582143383374097, 360582143086463691]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573105936630579, 360573157412667979⟩, ⟨792358981185906678, 795437105340181248⟩, true⟩

def words04 : List Nat := [360582142789268184, 360582142567332642, 360582142409568864, 360582142193990938, 360582141978318772, 360582141654751938, 360582141203513971, 360582140879999254, 360582140556116631, 360582140327465723]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885A
