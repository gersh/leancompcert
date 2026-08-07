import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk511

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472167072571269, 362472204869560076⟩, ⟨654159352696012202, 655464190093193284⟩, true⟩

def state01 : KState := ⟨⟨362495251975934061, 362495289788210884⟩, ⟨(-525555345370183184), (-524249726676815276)⟩, true⟩

def words00 : List Nat := [371285031796267403, 371285031798172029, 371285031929764359, 371285032124340359, 371285032253856709, 371285032255579050, 371285032121774004, 371285032122626027, 371285032503584577, 371285032706043116]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492467485796773, 362492505313675292⟩, ⟨(-383153491655797516), (-381847075481609492)⟩, true⟩

def words01 : List Nat := [371285032905160427, 371285033104847297, 371285033649154159, 371285034054559419, 371285034577008439, 371285035100083260, 371285035547487602, 371285035549196757, 371285035689538756, 371285035837814460]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461762230705490, 362461800073822656⟩, ⟨1186659990785825406, 1187967186039231382⟩, true⟩

def words02 : List Nat := [371285036096221529, 371285036097930502, 371285035846929883, 371285035597231944, 371285035346907705, 371285035207884434, 371285034876852421, 371285034704579077, 371285034531699184, 371285034323500717]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493545566888055, 362493583425427954⟩, ⟨(-438537074663472567), (-437229090766627275)⟩, true⟩

def words03 : List Nat := [371285033870254717, 371285033799735561, 371285034037643018, 371285034039353259, 371285033910056970, 371285033691196486, 371285033632678416, 371285033634581129, 371285033773724596, 371285033942806054]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487801958343362, 362487839832323812⟩, ⟨(-144774737117710126), (-143465963512220934)⟩, true⟩

def words04 : List Nat := [371285034111960290, 371285034113707819, 371285034374833871, 371285034686385062, 371285035094367026, 371285035096076942, 371285035039397285, 371285034981491548, 371285035021686237, 371285035078486894]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474737589655099, 362474775479045340⟩, ⟨523616139582868244, 524925701476075296⟩, true⟩

def words05 : List Nat := [371285035516031939, 371285035954279059, 371285036322844042, 371285036324553977, 371285036184161989, 371285036112299946, 371285036347058314, 371285036348768335, 371285036148770070, 371285035950145342]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481427370666393, 362481465275390638⟩, ⟨181309839161755691, 182620185618741769⟩, true⟩

def words06 : List Nat := [371285035750761514, 371285035748502753, 371285035554505126, 371285035519693037, 371285035484380282, 371285035383406949, 371285034773269993, 371285034444494292, 371285034165231809, 371285034167038454]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475812324166243, 362475850244435846⟩, ⟨468697307255471345, 470008449249630347⟩, true⟩

def words07 : List Nat := [371285034098574209, 371285033998014901, 371285034137538023, 371285034190184146, 371285034271558888, 371285034353595923, 371285034360996535, 371285034362707251, 371285033861580483, 371285033684241427]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362452896298420729, 362452934233930935⟩, ⟨1641658499020906537, 1642970421108411429⟩, true⟩

def words08 : List Nat := [371285033514844093, 371285033516555100, 371285033062978655, 371285032527683603, 371285031991702076, 371285031519315468, 371285030901260807, 371285030525921544, 371285030150035873, 371285029768627330]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496700003296225, 362496737954326942⟩, ⟨(-600923222437509656), (-599610505779916458)⟩, true⟩

def words09 : List Nat := [371285029142833390, 371285028628587533, 371285028113440328, 371285027979825287, 371285027620484723, 371285027197521470, 371285026773895460, 371285026731944737, 371285026809686266, 371285027040364717]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk511
