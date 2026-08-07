import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk356

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362515013695707605, 362515031508800396⟩, ⟨(-1068426568215356325), (-1067997992487379275)⟩, true⟩

def state01 : KState := ⟨⟨362499120974601153, 362499138798134249⟩, ⟨(-502553209278407183), (-502124261821759949)⟩, true⟩

def words00 : List Nat := [371285033247755438, 371285033434086556, 371285034408942254, 371285035384343926, 371285036600107407, 371285037004604881, 371285037275325539, 371285037546421538, 371285038143577199, 371285038540859201]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490643988409847, 362490661822355151⟩, ⟨(-200570177182580979), (-200140858894911571)⟩, true⟩

def words01 : List Nat := [371285039607655965, 371285040674853630, 371285041736493440, 371285041747974683, 371285041813179323, 371285041878990043, 371285042732376182, 371285042884826106, 371285043043438476, 371285043202470956]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495534263661969, 362495552107968485⟩, ⟨(-374683096956524692), (-374253409548656636)⟩, true⟩

def words02 : List Nat := [371285044094274474, 371285044592426969, 371285045407859076, 371285046223712483, 371285046958163989, 371285046959321783, 371285047196118543, 371285047594607863, 371285048222114657, 371285048518129619]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490740473011968, 362490758327882362⟩, ⟨(-203830220265181499), (-203400156415441461)⟩, true⟩

def words03 : List Nat := [371285048725691219, 371285048933641761, 371285049664193270, 371285050003585186, 371285050583370353, 371285051163555891, 371285051594776661, 371285051595934706, 371285051251318831, 371285051412913213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482442929737553, 362482460794922152⟩, ⟨91963946703963184, 92394378204542186⟩, true⟩

def words04 : List Nat := [371285052155528780, 371285052156687008, 371285051965066116, 371285051777377914, 371285051641265143, 371285051642546755, 371285051806807967, 371285052212156319, 371285052501382837, 371285052502585674]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501242036935008, 362501259912581043⟩, ⟨(-578387884077180777), (-577957079571776905)⟩, true⟩

def words05 : List Nat := [371285052456786859, 371285052484250703, 371285053164720043, 371285053165878557, 371285052798499164, 371285052306764515, 371285052054426834, 371285052055736776, 371285052477764047, 371285052933540305]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488787096753224, 362488804982842112⟩, ⟨(-134261858829709844), (-133830681878351996)⟩, true⟩

def words06 : List Nat := [371285053385626843, 371285053386793326, 371285053467543155, 371285053796858312, 371285054158102699, 371285054159264639, 371285053720077537, 371285053277958798, 371285053070056580, 371285053176560305]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465383206688143, 362465401103240342⟩, ⟨700808132020124230, 701239682250892492⟩, true⟩

def words07 : List Nat := [371285054068196105, 371285054960291514, 371285055640292770, 371285055641452117, 371285055274668129, 371285055133081773, 371285055633343408, 371285055634502798, 371285055231304804, 371285054681778764]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503535302911572, 362503553209837250⟩, ⟨(-660602993687436919), (-660171073277496063)⟩, true⟩

def words08 : List Nat := [371285054235654780, 371285054236934507, 371285054341569301, 371285054641329298, 371285054849460834, 371285054850640563, 371285054660260247, 371285054913637536, 371285055840374099, 371285056359839282]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492742912635901, 362492760830136742⟩, ⟨(-275361788977514801), (-274929491087691879)⟩, true⟩

def words09 : List Nat := [371285056875879032, 371285057392270835, 371285058232668158, 371285058683104052, 371285059083789004, 371285059484906541, 371285059870007281, 371285059871172881, 371285059722491433, 371285059939655028]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk356
