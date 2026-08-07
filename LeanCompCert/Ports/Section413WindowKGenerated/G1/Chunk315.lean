import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk315

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362458348119257237, 362458361924832384⟩, ⟨849891287357474067, 850185229312891689⟩, true⟩

def state01 : KState := ⟨⟨362436724741491322, 362436738556087580⟩, ⟨1531181323473849266, 1531475549641238074⟩, true⟩

def words00 : List Nat := [371285351076003748, 371285350817447996, 371285349517746258, 371285348222105062, 371285346926138303, 371285345940698681, 371285344500022731, 371285343468767166, 371285342437252526, 371285341398031130]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362510141310016934, 362510155133790755⟩, ⟨(-782508093205550730), (-782213577807279426)⟩, true⟩

def words01 : List Nat := [371285339856310800, 371285339318907461, 371285339246055033, 371285339247086572, 371285338878262053, 371285338238699772, 371285337961630726, 371285337962761126, 371285338712021921, 371285339500473054]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478754851585080, 362478768684517766⟩, ⟨206819062933394094, 207113867066059858⟩, true⟩

def words02 : List Nat := [371285340121253407, 371285340122267787, 371285339436137075, 371285339469774828, 371285339613820221, 371285339614841560, 371285338856078557, 371285338141487506, 371285337470772250, 371285337471928679]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441163012115862, 362441176854176866⟩, ⟨1392428518958030454, 1392723610952460506⟩, true⟩

def words03 : List Nat := [371285338058319554, 371285338853390691, 371285339575444363, 371285339576459192, 371285338960238356, 371285338217303364, 371285337473870182, 371285337031837157, 371285335628241689, 371285334229286329]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470961906358640, 362470975757508336⟩, ⟨452603018537220550, 452898397236434948⟩, true⟩

def words04 : List Nat := [371285332829976345, 371285332432984179, 371285331916046359, 371285332159196678, 371285332251962761, 371285332252978122, 371285331008394242, 371285330765867977, 371285330697731519, 371285330698783659]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461638716867174, 362461652577282720⟩, ⟨746909215578315202, 747204886661370260⟩, true⟩

def words05 : List Nat := [371285330244570927, 371285329763345987, 371285329666332277, 371285329667461123, 371285329756104365, 371285329956436615, 371285330048431086, 371285330049447527, 371285329019714773, 371285328270776427]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362451307348648871, 362451321218126888⟩, ⟨1072998481347543483, 1073294438489263967⟩, true⟩

def words06 : List Nat := [371285327541329818, 371285327542346021, 371285326406586104, 371285325044366827, 371285323681849899, 371285322474278323, 371285320763510548, 371285320053607022, 371285319343395208, 371285318507911154]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481077843000251, 362481091721639664⟩, ⟨133059898300869878, 133356144715616614⟩, true⟩

def words07 : List Nat := [371285317431749392, 371285317243058895, 371285317863997120, 371285317865013534, 371285317340930617, 371285316656228506, 371285315971163711, 371285315497057814, 371285314658052253, 371285314525462198]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362460340633038064, 362460354520865285⟩, ⟨787907012347577159, 788203548957859839⟩, true⟩

def words08 : List Nat := [371285314392522055, 371285314007176095, 371285312287249531, 371285311567323010, 371285310846905008, 371285310436646429, 371285309008279481, 371285307584353553, 371285306160114552, 371285305567049453]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362439229804014319, 362439243701012838⟩, ⟨1454932807061471014, 1455229633440133380⟩, true⟩

def words09 : List Nat := [371285304777936805, 371285304406573885, 371285304034875588, 371285303667750473, 371285301967215417, 371285300456194837, 371285298944757096, 371285298175293636, 371285296727908683, 371285295271691324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk315
