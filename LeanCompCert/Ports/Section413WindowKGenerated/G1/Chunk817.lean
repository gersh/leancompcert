import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472935481213337, 362473035733791975⟩, ⟨989731037359064076, 995261701573505594⟩, true⟩

def state01 : KState := ⟨⟨362489930897998552, 362490031175896030⟩, ⟨(-398833082870648056), (-393300349977281120)⟩, true⟩

def words00 : List Nat := [371285217493110570, 371285217496269268, 371285217532402485, 371285217627571440, 371285217707113162, 371285217709942268, 371285217617033943, 371285217647905276, 371285217804346603, 371285217866182806]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485547659569640, 362485647963336502⟩, ⟨(-40634375633563568), (-35099528822568704)⟩, true⟩

def words01 : List Nat := [371285217897255818, 371285217929263808, 371285218073009854, 371285218143186013, 371285218239542981, 371285218336958062, 371285218433327193, 371285218442918278, 371285218450118746, 371285218458939560]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485614377944099, 362485714706885657⟩, ⟨(-46081027814840241), (-40544123595104329)⟩, true⟩

def words02 : List Nat := [371285218597052512, 371285218599884856, 371285218575433785, 371285218551818071, 371285218527181550, 371285218513521305, 371285218496051295, 371285218564332377, 371285218629990075, 371285218639009391]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495957969858066, 362496058324373221⟩, ⟨(-891514922041691223), (-885975927563776735)⟩, true⟩

def words03 : List Nat := [371285218746285145, 371285218855045557, 371285219059977288, 371285219066296934, 371285219068487064, 371285219050733250, 371285219160626379, 371285219234770383, 371285219369327933, 371285219505083468]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494102012273049, 362494202392320420⟩, ⟨(-739855860669041947), (-734314779059520395)⟩, true⟩

def words04 : List Nat := [371285219611948455, 371285219614783050, 371285219627566628, 371285219698438379, 371285219813742886, 371285219816622846, 371285219808008312, 371285219805282990, 371285219945306499, 371285220058415520]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477744932448133, 362477845338065182⟩, ⟨597467750882506565, 603010922940228881⟩, true⟩

def words05 : List Nat := [371285220283113399, 371285220509002702, 371285220683231625, 371285220686063680, 371285220730439982, 371285220777178909, 371285220888390129, 371285220891221111, 371285220803211496, 371285220716281183]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484756969243884, 362484857400169448⟩, ⟨24145315369489396, 29690556783027564⟩, true⟩

def words06 : List Nat := [371285220687394860, 371285220690514744, 371285220738168306, 371285220802232530, 371285220833268718, 371285220836099874, 371285220667513872, 371285220561992505, 371285220495622203, 371285220498576970]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492906051130649, 362493006507827542⟩, ⟨(-642231406847625622), (-636684057984732528)⟩, true⟩

def words07 : List Nat := [371285220496253288, 371285220481876376, 371285220598514804, 371285220693980781, 371285220832069636, 371285220971281578, 371285221109392673, 371285221112226510, 371285221177152104, 371285221275830077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477745836676200, 362477846318612764⟩, ⟨597648266961870741, 603197680056228417⟩, true⟩

def words08 : List Nat := [371285221436099385, 371285221438931483, 371285221416681227, 371285221390788174, 371285221363798987, 371285221343719016, 371285221258487357, 371285221264685091, 371285221272032976, 371285221274965084]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497342547911220, 362497443055483355⟩, ⟨(-1005270688805218996), (-999719178853090508)⟩, true⟩

def words09 : List Nat := [371285221227263061, 371285221271272349, 371285221450131795, 371285221452964198, 371285221432911418, 371285221375767214, 371285221392024542, 371285221395146278, 371285221546417010, 371285221699034741]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817
