import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344

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

def state06 : KState := ⟨⟨360636938057006649, 360636945282890507⟩, ⟨(-1908217363274313791), (-1908049013074452243)⟩, true⟩

def words05 : List Nat := [360581570413034047, 360581570248122531, 360581570547523531, 360581571332717689, 360581571400755878, 360581571468826513, 360581572377908516, 360581573709646189, 360581575316856498, 360581576924076937]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590636659283169, 360590643889570401⟩, ⟨(-312837748161021934), (-312669246198895698)⟩, true⟩

def words06 : List Nat := [360581577862431961, 360581577961865725, 360581577962243198, 360581577774652083, 360581577586949889, 360581577060046493, 360581576183756052, 360581574884001063, 360581573584225234, 360581573388389731]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550497977426247, 360550505212059409⟩, ⟨1071145271983045712, 1071313923771208458⟩, true⟩

def words07 : List Nat := [360581574492406424, 360581575596447787, 360581576277021092, 360581576837917942, 360581576838311402, 360581576820654129, 360581577171105398, 360581577171567142, 360581576702163445, 360581575801495929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588233819068042, 360588241058065183⟩, ⟨(-230052974126244719), (-229884171846604809)⟩, true⟩

def words08 : List Nat := [360581574900776742, 360581574186674136, 360581574915954231, 360581575700774375, 360581575701203659, 360581575696870118, 360581575513749611, 360581575842387326, 360581575842768964, 360581576010028113]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586403545116789, 360586410788508432⟩, ⟨(-166974180744992877), (-166805226876605241)⟩, true⟩

def words09 : List Nat := [360581576010439444, 360581575781302976, 360581575598339404, 360581576066442750, 360581576321726243, 360581576577081576, 360581576577496763, 360581576412373459, 360581575853868351, 360581575994535023]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344
