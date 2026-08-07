import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360561688637367564, 360561691082001469⟩, ⟨417591139199999008, 417625052786692942⟩, true⟩

def state01 : KState := ⟨⟨360609153558688171, 360609156005810163⟩, ⟨(-556051063376602803), (-556017098771795115)⟩, true⟩

def words00 : List Nat := [360582062042304936, 360582060953232243, 360582060953449011, 360582060343250895, 360582059733089949, 360582057077356108, 360582052051443007, 360582049393301238, 360582046735341940, 360582047766388790]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532215219184406, 360532217668816064⟩, ⟨1022507221406778954, 1022541237496905606⟩, true⟩

def words01 : List Nat := [360582047766625606, 360582047579792040, 360582048888274729, 360582051908028870, 360582053335472779, 360582054762819433, 360582054763058028, 360582054336594889, 360582051541386231, 360582049113138526]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360556174482407819, 360556176934519084⟩, ⟨530779190250933470, 530813257235423334⟩, true⟩

def words02 : List Nat := [360582046685037076, 360582046621762056, 360582045289154915, 360582042768481635, 360582040248006850, 360582037067789427, 360582035698039731, 360582035008001103, 360582034318003005, 360582032426834497]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545772834403202, 360545775289006324⟩, ⟨744308991417992131, 744343109572477175⟩, true⟩

def words03 : List Nat := [360582031167712223, 360582029734658259, 360582029230221241, 360582029230484830, 360582027794196719, 360582024134216427, 360582020474542924, 360582017152941684, 360582015763418128, 360582013999306835]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360497343300961404, 360497345758071886⟩, ⟨1738807889110105232, 1738842058778423436⟩, true⟩

def words04 : List Nat := [360582012235328216, 360582008924979746, 360582003251288185, 360581999937940024, 360581996624848634, 360581991625196499, 360581984262848540, 360581975702631274, 360581967143195096, 360581960943413902]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360436118142828550, 360436120602427473⟩, ⟨2997560866806936654, 2997595087625101560⟩, true⟩

def words05 : List Nat := [360581956826300400, 360581955068148403, 360581953310136113, 360581949755060587, 360581944877284182, 360581939403408165, 360581933929985180, 360581929989446667, 360581925120254675, 360581918028868383]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360631073700839817, 360631076162930913⟩, ⟨(-1011834845109995392), (-1011800573040590646)⟩, true⟩

def words06 : List Nat := [360581910938112595, 360581905078071637, 360581900803665565, 360581898884787106, 360581896966076675, 360581893042200634, 360581890142899059, 360581888908116821, 360581887996731926, 360581890388148910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554688676793988, 360554691141402259⟩, ⟨559861582276548731, 559895906136493493⟩, true⟩

def words07 : List Nat := [360581891597661948, 360581892807086456, 360581893959448655, 360581896387223379, 360581898163445526, 360581899939537847, 360581900292436879, 360581900292701087, 360581898289458000, 360581896967745141]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360492402583568433, 360492405050662575⟩, ⟨1841909115910468599, 1841943490942206663⟩, true⟩

def words08 : List Nat := [360581895646069926, 360581894665258818, 360581892465557942, 360581889069054627, 360581885672838377, 360581880958689816, 360581877633099962, 360581873217886730, 360581868803073506, 360581863209523295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360634417349910172, 360634419819500136⟩, ⟨(-1082993136194517573), (-1082958709761280981)⟩, true⟩

def words09 : List Nat := [360581858865210099, 360581855986171110, 360581853107328738, 360581852575982656, 360581852149756047, 360581849698449944, 360581847247330919, 360581846455753656, 360581849008072691, 360581851560203924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205
