import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477256013975437, 362477302424837675⟩, ⟨427001480555202544, 428769718436653566⟩, true⟩

def state01 : KState := ⟨⟨362469971975009718, 362470018402785554⟩, ⟨837894584054989586, 839663775952077046⟩, true⟩

def words00 : List Nat := [371284904770647070, 371284904772546658, 371284904534547115, 371284904295614664, 371284904055981992, 371284903875744664, 371284903604991024, 371284903543348137, 371284903481036050, 371284903419200234]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479998183394178, 362480044628356638⟩, ⟨272284413183900166, 274054574664006428⟩, true⟩

def words01 : List Nat := [371284903156625029, 371284903127902491, 371284903196890003, 371284903198790476, 371284902927150399, 371284902606377741, 371284902284815997, 371284902278014396, 371284902113468515, 371284902029538205]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459077301138690, 362459123763247747⟩, ⟨1452668913866756331, 1454440042845509229⟩, true⟩

def words02 : List Nat := [371284901944880383, 371284901860749966, 371284901357546891, 371284901050883669, 371284900743278377, 371284900478637726, 371284899834166989, 371284899128490879, 371284898422084691, 371284897997570723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464402878467411, 362464449357689315⟩, ⟨1152212951704959532, 1153985046450881502⟩, true⟩

def words03 : List Nat := [371284897542121483, 371284897401286388, 371284897259797325, 371284897113056258, 371284896760711641, 371284896504923217, 371284896303894050, 371284896305795132, 371284895944706192, 371284895584593123]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474823789375504, 362474870285654236⟩, ⟨564014990547851141, 565788048062809811⟩, true⟩

def words04 : List Nat := [371284895223656014, 371284894899334069, 371284894445601153, 371284894306318013, 371284894166466098, 371284893976921111, 371284893501523809, 371284893291636594, 371284893101187207, 371284893103157564]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465877475612922, 362465923989171538⟩, ⟨1069150707997850792, 1070924741052043370⟩, true⟩

def words05 : List Nat := [371284892927031413, 371284892752579315, 371284892714422599, 371284892716517992, 371284892704458397, 371284892708434440, 371284892709875550, 371284892649993609, 371284892171557453, 371284891837932644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362460135602484953, 362460182133002319⟩, ⟨1393423974454690684, 1395198965088953466⟩, true⟩

def words06 : List Nat := [371284891503277023, 371284891451060892, 371284891183120291, 371284890813887600, 371284890443917482, 371284890112610093, 371284889624030206, 371284889449636388, 371284889274644933, 371284889038706037]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505256994987680, 362505303542722775⟩, ⟨(-1154801646101627515), (-1153025683095565355)⟩, true⟩

def words07 : List Nat := [371284888602481872, 371284888441259280, 371284888428870952, 371284888430791455, 371284888376139988, 371284888269571222, 371284888366886920, 371284888417132243, 371284888779880712, 371284889143489484]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483638750200209, 362483685315119012⟩, ⟨66223118882951279, 68000052512049491⟩, true⟩

def words08 : List Nat := [371284889483937530, 371284889485841673, 371284889589278333, 371284889707215196, 371284889820872333, 371284889822775558, 371284889565302899, 371284889295649472, 371284889066717304, 371284889068925209]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472377655889774, 362472424237922942⟩, ⟨702472875001472077, 704250775507076605⟩, true⟩

def words09 : List Nat := [371284889222873945, 371284889398879842, 371284889574603879, 371284889576507831, 371284889393928498, 371284889307717492, 371284889262240118, 371284889264153934, 371284889071912856, 371284888853418643]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564
