import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502921503369566, 362503013042214146⟩, ⟨(-1394941117991291108), (-1390107237098793372)⟩, true⟩

def state01 : KState := ⟨⟨362497942326361998, 362498033889591037⟩, ⟨(-1005590352452226153), (-1000754564575573941)⟩, true⟩

def words00 : List Nat := [371285237190784502, 371285237225171474, 371285237422106531, 371285237620469998, 371285237867573287, 371285237897632475, 371285237930521699, 371285237964375477, 371285238149796850, 371285238316531294]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486417054009966, 362486508641505696⟩, ⟨(-104124936495418183), (-99287250592565007)⟩, true⟩

def words01 : List Nat := [371285238549984598, 371285238784473840, 371285239010558463, 371285239019521506, 371285239077810907, 371285239137457592, 371285239269376109, 371285239286933618, 371285239305200293, 371285239324434928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484687730273926, 362484779341916783⟩, ⟨31140642590075001, 35980217405497683⟩, true⟩

def words02 : List Nat := [371285239387562931, 371285239390537557, 371285239427971874, 371285239486980859, 371285239498036219, 371285239500735681, 371285239293761530, 371285239232204855, 371285239267760778, 371285239270555483]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485593994275161, 362485685630579229⟩, ⟨(-39711687256980996), (-34870183074601530)⟩, true⟩

def words03 : List Nat := [371285239266694647, 371285239262616119, 371285239413532253, 371285239522531317, 371285239680511490, 371285239839497239, 371285239996920566, 371285239999620542, 371285239944894431, 371285239953976494]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486500885584156, 362486592545940742⟩, ⟨(-110629297909350264), (-105785911735332216)⟩, true⟩

def words04 : List Nat := [371285240124759536, 371285240172067055, 371285240186799477, 371285240202407391, 371285240267098612, 371285240282168903, 371285240403197109, 371285240525336360, 371285240646506237, 371285240666581561]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782A
