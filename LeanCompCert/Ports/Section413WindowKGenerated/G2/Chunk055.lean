import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk055

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360055277068429546, 360055277223183961⟩, ⟨2869178733912077070, 2869179311659817084⟩, true⟩

def state01 : KState := ⟨⟨360500174381355455, 360500174536701575⟩, ⟨420844816913098416, 420845397918190204⟩, true⟩

def words00 : List Nat := [360576851357330359, 360576789245040234, 360576753181285845, 360576749803724707, 360576746427385785, 360576714528752291, 360576650016746173, 360576618173259635, 360576586341315716, 360576553011822844]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360493733808328410, 360493733964272018⟩, ⟨455762772937547308, 455763357237810762⟩, true⟩

def words01 : List Nat := [360576539152602219, 360576499528694680, 360576459919149826, 360576435291395148, 360576427606023276, 360576411460387434, 360576395320597338, 360576362219011735, 360576314750074482, 360576299789858578]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659278508169547, 360659278664706539⟩, ⟨(-459087897581825783), (-459087310003122059)⟩, true⟩

def words02 : List Nat := [360576302365440631, 360576317219751532, 360576317219808526, 360576306440885698, 360576295665855049, 360576260079819470, 360576255543923445, 360576269488798394, 360576269488854647, 360576276077470394]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360704522425489434, 360704522582620844⟩, ⟨(-709591372630899694), (-709590781762103984)⟩, true⟩

def words03 : List Nat := [360576323483853940, 360576370873119703, 360576422304827435, 360576441425448691, 360576441425507341, 360576430581389225, 360576419741177088, 360576414479640766, 360576437603898268, 360576460719823136]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360679553645569285, 360679553803301767⟩, ⟨(-572413142706834752), (-572412548505156018)⟩, true⟩

def words04 : List Nat := [360576467307464848, 360576467307528089, 360576479091423495, 360576491455707716, 360576495527888919, 360576495527952091, 360576485755854137, 360576457008733257, 360576428271961593, 360576434987141588]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360252835983425757, 360252836141754485⟩, ⟨1797385022022124625, 1797385619536030285⟩, true⟩

def words05 : List Nat := [360576437347559180, 360576439707137496, 360576439707194350, 360576425508186482, 360576379258868646, 360576309106272176, 360576238978905969, 360576200943597646, 360576165089258034, 360576106936635066]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360797493129327390, 360797493288254838⟩, ⟨(-1233723172253629847), (-1233722571407889827)⟩, true⟩

def words06 : List Nat := [360576048804912557, 360576008902413225, 360575996659848584, 360576006542104595, 360576006542164012, 360575986076471670, 360575971735025113, 360575970215688610, 360575999110198587, 360576038868687815]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583401691166238, 360583401850699817⟩, ⟨(-39217392520804426), (-39216788295875938)⟩, true⟩

def words07 : List Nat := [360576062271561871, 360576085666044683, 360576140949494460, 360576212782715879, 360576273944457951, 360576335084276811, 360576369667957769, 360576372492572085, 360576373752366112, 360576375011729046]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360674476050706224, 360674476210838937⟩, ⟨(-548297425885076201), (-548296818314000509)⟩, true⟩

def words08 : List Nat := [360576408078082761, 360576409408412424, 360576409408469125, 360576394432382954, 360576379461649550, 360576358771954861, 360576376220239692, 360576393662293081, 360576393662350458, 360576408455819442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360626100542070719, 360626100702805584⟩, ⟨(-277823035765586068), (-277822424825417670)⟩, true⟩

def words09 : List Nat := [360576457669080293, 360576506864761230, 360576539546614337, 360576540588392056, 360576540588450790, 360576514089101983, 360576487599210390, 360576480694680411, 360576489555448256, 360576498413067070]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk055
