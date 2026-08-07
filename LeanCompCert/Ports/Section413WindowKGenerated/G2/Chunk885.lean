import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885

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

def state06 : KState := ⟨⟨360553273617646464, 360553325105837132⟩, ⟨2548649290675073427, 2551728491061379621⟩, true⟩

def words05 : List Nat := [360582140227169878, 360582140063600838, 360582139899793749, 360582139779522769, 360582139722941132, 360582139619438825, 360582139515813379, 360582139314428797, 360582138985405967, 360582138661517591]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544322591662058, 360544374091866974⟩, ⟨3341316949730096985, 3344397214159254557⟩, true⟩

def words06 : List Nat := [360582138337203768, 360582137995650744, 360582137526571568, 360582136982543719, 360582136438297685, 360582135862316084, 360582135364373753, 360582134944858146, 360582134525229018, 360582134024283812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559732832368673, 360559784344639332⟩, ⟨1976270215242982959, 1979351548391755759⟩, true⟩

def words07 : List Nat := [360582133599009690, 360582133171209823, 360582132743036282, 360582132375241110, 360582131917089575, 360582131349809909, 360582130782298446, 360582130310695499, 360582129950610107, 360582129699667463]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546474141252058, 360546525665669180⟩, ⟨3150695571863598264, 3153777981008456744⟩, true⟩

def words08 : List Nat := [360582129448545750, 360582129133735046, 360582128781986789, 360582128450250907, 360582128118202521, 360582127698687139, 360582127151727489, 360582126516079209, 360582125880200613, 360582125371967955]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531845328010338, 360531896864471530⟩, ⟨4446810729323285717, 4449894205512185749⟩, true⟩

def words09 : List Nat := [360582124971156500, 360582124697825659, 360582124424339089, 360582124087188648, 360582123730323181, 360582123280850418, 360582122830999658, 360582122437566672, 360582121969588538, 360582121404037131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885
