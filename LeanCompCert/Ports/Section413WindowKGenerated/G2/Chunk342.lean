import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk342

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545436383341948, 360545443496157673⟩, ⟨1232632212236588278, 1232796680792737964⟩, true⟩

def state01 : KState := ⟨⟨360568170533886865, 360568177651021381⟩, ⟨454968202084174455, 455132818364479047⟩, true⟩

def words00 : List Nat := [360581489129135628, 360581488464379349, 360581487867479902, 360581486730446357, 360581485593403480, 360581484239848763, 360581483315289073, 360581483006952434, 360581482698595054, 360581481738082606]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360629174468256828, 360629181589711289⟩, ⟨(-1632288891033305757), (-1632124126945670669)⟩, true⟩

def words01 : List Nat := [360581481813911162, 360581482278729801, 360581483596539515, 360581484063369566, 360581484063791845, 360581483803449125, 360581484135277103, 360581485159193311, 360581486553382044, 360581487947592542]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568859232718188, 360568866358542782⟩, ⟨431702959291928757, 431867872946615193⟩, true⟩

def words02 : List Nat := [360581488519324335, 360581488530421471, 360581488530798564, 360581488514652367, 360581488498385640, 360581488096740382, 360581487083106844, 360581485643230428, 360581484203352122, 360581483006890624]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360520948948020086, 360520956078158630⟩, ⟨2072033147003191443, 2072198208346115741⟩, true⟩

def words03 : List Nat := [360581483122352314, 360581483606450194, 360581483660888265, 360581483661346686, 360581482865911485, 360581481641155193, 360581480416337841, 360581478934561257, 360581477652740192, 360581475885645375]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360547692044920812, 360547699179385793⟩, ⟨1156251539153953538, 1156416748655610314⟩, true⟩

def words04 : List Nat := [360581474118550194, 360581472940152971, 360581472307401676, 360581471776359469, 360581471245308391, 360581469986890561, 360581467878952362, 360581466160017542, 360581464441049334, 360581463172047271]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360563501040843243, 360563508179682681⟩, ⟨614619599234124104, 614784958582446230⟩, true⟩

def words05 : List Nat := [360581462186681748, 360581460524009352, 360581458861346359, 360581458050032016, 360581457893164256, 360581457026662960, 360581456160163042, 360581454763793375, 360581453389428206, 360581452866156191]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578152637037658, 360578159780194779⟩, ⟨112518453129375445, 112683960423271511⟩, true⟩

def words06 : List Nat := [360581452669841045, 360581452670300135, 360581452525822781, 360581451899640895, 360581451273430050, 360581449832771703, 360581448819455565, 360581448656819030, 360581448494139744, 360581447902763302]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602326324573395, 360602333472069512⟩, ⟨(-715996535609368699), (-715830879596860019)⟩, true⟩

def words07 : List Nat := [360581448237121925, 360581448667549010, 360581449947998808, 360581450380422134, 360581450380845719, 360581450091298467, 360581450133554900, 360581450981074016, 360581451590626011, 360581452200239727]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608253321616713, 360608260473487387⟩, ⟨(-919406591800640597), (-919240785806718645)⟩, true⟩

def words08 : List Nat := [360581452274176824, 360581452274636047, 360581452141463028, 360581452500061678, 360581452643113237, 360581453051451090, 360581453051862816, 360581452819888408, 360581452634352627, 360581453416655953]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585920069613239, 360585927225815683⟩, ⟨(-153433773718270179), (-153267819166267367)⟩, true⟩

def words09 : List Nat := [360581454775926446, 360581456135205421, 360581456754222521, 360581457129620528, 360581457130005830, 360581457115081148, 360581457933560496, 360581458645100570, 360581458775793089, 360581458906549007]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk342
