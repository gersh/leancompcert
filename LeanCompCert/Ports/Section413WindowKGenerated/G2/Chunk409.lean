import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk409

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565768183656783, 360565778506205505⟩, ⟨679837860292063451, 680123198837662287⟩, true⟩

def state01 : KState := ⟨⟨360586815893220268, 360586826221014700⟩, ⟨(-181069387217005212), (-180783834095564718)⟩, true⟩

def words00 : List Nat := [360582407029163870, 360582406608758953, 360582407201136136, 360582407795765556, 360582407856722970, 360582407857278263, 360582407464358318, 360582407332463717, 360582407200405521, 360582407266843559]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551810849524561, 360551821182606415⟩, ⟨1251234859832763920, 1251520629288293918⟩, true⟩

def words01 : List Nat := [360582407267340629, 360582407000067204, 360582406912114530, 360582407394294068, 360582407451923317, 360582407509632282, 360582407510127801, 360582407174673570, 360582406500018576, 360582405753214634]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587618097942995, 360587628436259191⟩, ⟨(-214119220141740283), (-213833236470361081)⟩, true⟩

def words02 : List Nat := [360582405006258635, 360582404714982327, 360582404639274459, 360582404263751492, 360582403888154259, 360582403363197362, 360582403650910660, 360582404092862227, 360582404093365707, 360582404199458958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608913274321107, 360608923617881422⟩, ⟨(-1085939232914541128), (-1085653034575317306)⟩, true⟩

def words03 : List Nat := [360582404305659612, 360582404412020924, 360582405113645470, 360582405416874914, 360582405417387191, 360582405215429799, 360582405013367051, 360582404819753606, 360582405467950881, 360582406116243082]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600128996396184, 360600139345262386⟩, ⟨(-726497388233873906), (-726210972646855226)⟩, true⟩

def words04 : List Nat := [360582406465187696, 360582406729262753, 360582406978876955, 360582407228633977, 360582407229100135, 360582407188476438, 360582406780783604, 360582406073999487, 360582405367143089, 360582405688632589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360519314153469735, 360519324507565222⟩, ⟨2583411255938815295, 2583697885691910241⟩, true⟩

def words05 : List Nat := [360582406480853802, 360582407273142356, 360582407528620222, 360582407529176198, 360582407191068210, 360582406700937735, 360582406210676210, 360582405706440752, 360582404608693740, 360582403069227623]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555057839034506, 360555068198379466⟩, ⟨1119145051111523326, 1119431895908966862⟩, true⟩

def words06 : List Nat := [360582401529710949, 360582400585066592, 360582399938829815, 360582399184168400, 360582398429485799, 360582397170827412, 360582395318860351, 360582393880207258, 360582392441456069, 360582391407945221]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554989132485064, 360554999497131774⟩, ⟨1121914732295727183, 1122201794332724249⟩, true⟩

def words07 : List Nat := [360582390741557857, 360582389613111734, 360582388484614330, 360582387950655845, 360582387714829977, 360582387052740282, 360582386390624672, 360582385337656477, 360582384298331105, 360582383630717248]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546953170851725, 360546963540738070⟩, ⟨1451263770950327465, 1451551047733387279⟩, true⟩

def words08 : List Nat := [360582382962951822, 360582382752371959, 360582382189245668, 360582381262415803, 360582380335548352, 360582378997347366, 360582378154767287, 360582377514631435, 360582376874468521, 360582375861980651]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566664743221222, 360566675118363760⟩, ⟨643251954724432493, 643539446985396889⟩, true⟩

def words09 : List Nat := [360582374998525958, 360582374593319513, 360582374375887887, 360582374376444464, 360582374131083676, 360582373374884438, 360582372618618404, 360582371952936971, 360582371584700291, 360582371202436575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk409
