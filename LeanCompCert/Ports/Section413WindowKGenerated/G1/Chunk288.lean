import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk288

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362527367614883071, 362527379068655510⟩, ⟨(-1214220372835944955), (-1213997389601626995)⟩, true⟩

def state01 : KState := ⟨⟨362502865725252507, 362502877187207785⟩, ⟨(-508388117014658235), (-508164898071677485)⟩, true⟩

def words00 : List Nat := [371285230354360904, 371285231258541566, 371285232163204138, 371285233068106985, 371285234019342582, 371285234368273484, 371285235921763767, 371285237475531821, 371285238696214666, 371285239309380856]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362538280242416481, 362538291712691357⟩, ⟨(-1528770144825788310), (-1528546686152707564)⟩, true⟩

def words01 : List Nat := [371285240920524995, 371285242532041011, 371285245347388551, 371285246558916463, 371285247506866628, 371285248455046441, 371285250606847563, 371285252164677122, 371285254005686894, 371285255846963149]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362514835958337320, 362514847436906188⟩, ⟨(-853156111938851658), (-852932414189915072)⟩, true⟩

def words02 : List Nat := [371285257675744970, 371285257901490978, 371285258589848562, 371285259278639562, 371285260334400239, 371285260643614037, 371285260942843939, 371285261242347949, 371285262544625185, 371285263571823815]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489972160043632, 362489983646927237⟩, ⟨(-136116869605986109), (-135892932101992245)⟩, true⟩

def words03 : List Nat := [371285265205603456, 371285266839654434, 371285268223429938, 371285268466770978, 371285269029438332, 371285269592521228, 371285271357690478, 371285271521592058, 371285271685669713, 371285271850106670]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362504111893209158, 362504123388336463⟩, ⟨(-543759809639910544), (-543535634345471722)⟩, true⟩

def words04 : List Nat := [371285273067592327, 371285274012557848, 371285276159078115, 371285278305814561, 371285280263074890, 371285280619889326, 371285281269639036, 371285281919817589, 371285283330732272, 371285283984698965]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500716922410196, 362500728425919971⟩, ⟨(-445827647715475894), (-445603230544173486)⟩, true⟩

def words05 : List Nat := [371285284501556417, 371285285018679357, 371285285887371760, 371285286319127307, 371285287008159754, 371285287697503573, 371285288386758415, 371285288387680253, 371285288257405883, 371285288793525246]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466767241055827, 362466778752789683⟩, ⟨534082149250218934, 534306803810802100⟩, true⟩

def words06 : List Nat := [371285289642544399, 371285289643466195, 371285288893606454, 371285288152528513, 371285287411130915, 371285286804418156, 371285285845402271, 371285285966761666, 371285286088302797, 371285286089256978]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362511115355535036, 362511126875610233⟩, ⟨(-746476655128739652), (-746251759711918594)⟩, true⟩

def words07 : List Nat := [371285286007876496, 371285286567987100, 371285287906950463, 371285287907872654, 371285287649234867, 371285286947465260, 371285286540314665, 371285286541330504, 371285287132188284, 371285288027934879]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498255705837159, 362498267234251808⟩, ⟨(-375064923719890554), (-374839787417195210)⟩, true⟩

def words08 : List Nat := [371285288913478474, 371285288914416703, 371285289457674415, 371285290110649932, 371285291063919438, 371285291300366192, 371285291536966787, 371285291773870922, 371285292508806723, 371285292958961331]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362456203899200943, 362456215435921207⟩, ⟨840216425055251455, 840441801348794119⟩, true⟩

def words09 : List Nat := [371285294448282183, 371285295937866439, 371285297427822207, 371285297428745056, 371285297576954394, 371285297831679404, 371285298448937708, 371285298449860661, 371285297472377481, 371285296467109747]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk288
