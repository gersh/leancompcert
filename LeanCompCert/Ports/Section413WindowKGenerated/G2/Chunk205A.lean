import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk205A
