import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk323

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465830366888395, 362465844912793108⟩, ⟨613651596894984316, 613969156763908898⟩, true⟩

def state01 : KState := ⟨⟨362440224251788397, 362440238807087062⟩, ⟨1440754505491575615, 1441072368833130569⟩, true⟩

def words00 : List Nat := [371284852658131188, 371284851907667124, 371284850082399583, 371284849212704004, 371284848342551484, 371284847475173869, 371284845571287372, 371284843476707438, 371284841381843464, 371284840242210341]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362430528991391909, 362430543556093737⟩, ⟨1754166606799197016, 1754484774004449106⟩, true⟩

def words01 : List Nat := [371284838862538182, 371284838326392761, 371284837789901027, 371284837256868951, 371284835578997739, 371284834024880648, 371284832470334805, 371284831521937142, 371284830035740824, 371284828357269618]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476810918542380, 362476825492559133⟩, ⟨258222095833435373, 258540564145815483⟩, true⟩

def words02 : List Nat := [371284826678424878, 371284825953979038, 371284824750238072, 371284824500810750, 371284824251085398, 371284823847420060, 371284822649771164, 371284822406438794, 371284822415827590, 371284822416906359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481787858539248, 362481802442060935⟩, ⟨97253407239889964, 97572182893095386⟩, true⟩

def words03 : List Nat := [371284822170344091, 371284821907629643, 371284821664383958, 371284821665534970, 371284821300239693, 371284821056829641, 371284820813076567, 371284820565557082, 371284819608348011, 371284819516361897]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460097449274317, 362460112042067512⟩, ⟨798940671872797659, 799259747415497713⟩, true⟩

def words04 : List Nat := [371284820283345090, 371284820284387801, 371284819996115030, 371284819711088222, 371284819433983576, 371284819435143645, 371284818972880725, 371284818907913195, 371284818842608257, 371284818680318378]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495393535521062, 362495408137746918⟩, ⟨(-343105363108652990), (-342785982370492736)⟩, true⟩

def words05 : List Nat := [371284817917327574, 371284817357564506, 371284817188515261, 371284817189576137, 371284816789395647, 371284816238501209, 371284815687231987, 371284815541281018, 371284815244651522, 371284815573167008]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483513137345917, 362483527749003103⟩, ⟨41292842286262707, 41612528269044979⟩, true⟩

def words06 : List Nat := [371284815632582046, 371284815633632222, 371284814991795826, 371284815147704401, 371284815597357991, 371284815598401258, 371284814777679546, 371284813960277461, 371284813275403770, 371284813276598687]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362454506094812602, 362454520715841357⟩, ⟨980534214141926735, 980854203531111545⟩, true⟩

def words07 : List Nat := [371284814149255606, 371284815061982527, 371284815798299956, 371284815799343602, 371284815265752729, 371284814698169923, 371284814512336464, 371284814513380152, 371284813626861043, 371284812692479131]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463544869069424, 362463559499459128⟩, ⟨687944545719800624, 688264838263318894⟩, true⟩

def words08 : List Nat := [371284811773138630, 371284811774318925, 371284811549850023, 371284811655089635, 371284811655899951, 371284811510632104, 371284810096043649, 371284809530301208, 371284808964078238, 371284808799806869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460667744457272, 362460682384383816⟩, ⟨781163307389130159, 781483908876685399⟩, true⟩

def words09 : List Nat := [371284808144570744, 371284807372243991, 371284806599532765, 371284806546699452, 371284806016761718, 371284805545260077, 371284805073420499, 371284804604748444, 371284803001256503, 371284802258114578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk323
