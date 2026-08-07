import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk078

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360720273414800749, 360720273737444175⟩, ⟨(-1075360722324312369), (-1075359015874486775)⟩, true⟩

def state01 : KState := ⟨⟨360669579473701350, 360669579797211584⟩, ⟨(-680168628721265572), (-680166915505985764)⟩, true⟩

def words00 : List Nat := [360582450224015824, 360582466866084930, 360582472132558492, 360582477397691613, 360582477397770094, 360582471936409035, 360582481612240796, 360582491285611880, 360582491285694165, 360582501713034656]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360734167342968284, 360734167667350387⟩, ⟨(-1185095854277820958), (-1185094134248922402)⟩, true⟩

def words01 : List Nat := [360582523093822060, 360582544469165555, 360582570042079434, 360582579427592157, 360582579427677169, 360582574812843859, 360582581833939980, 360582601720861880, 360582621102772564, 360582640479746638]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360839614710926815, 360839615036189118⟩, ⟨(-2011752893954768667), (-2011751167038422701)⟩, true⟩

def words02 : List Nat := [360582646990902629, 360582646990995002, 360582643935512961, 360582650518857944, 360582652431997333, 360582663093316744, 360582665465381424, 360582667836850448, 360582686406831628, 360582719216110147]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360467608585807812, 360467608911942209⟩, ⟨903505624886181950, 903507358635485704⟩, true⟩

def words03 : List Nat := [360582760242875542, 360582801259183669, 360582829502523740, 360582841623269557, 360582849483415827, 360582857341580323, 360582870175334465, 360582870175427015, 360582866898658991, 360582852197482450]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360431367853957969, 360431368180966072⟩, ⟨1188163908890837287, 1188165649494414145⟩, true⟩

def words04 : List Nat := [360582838951322038, 360582848605675683, 360582852195312241, 360582855784050656, 360582855784136002, 360582845530050678, 360582819202057072, 360582785261089634, 360582751328743132, 360582726862430329]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360449367396252661, 360449367724144196⟩, ⟨1047190135423720733, 1047191882966560907⟩, true⟩

def words05 : List Nat := [360582707583608199, 360582680073691348, 360582652570762795, 360582646430729739, 360582647448960630, 360582648466947382, 360582648467030885, 360582639845985595, 360582615196104681, 360582598243605591]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360317717754089747, 360317718082857204⟩, ⟨2081909585386488559, 2081911339818490521⟩, true⟩

def words06 : List Nat := [360582581295390624, 360582563842760607, 360582530371624718, 360582488715601027, 360582447070155921, 360582392150124407, 360582348651671455, 360582321199348616, 360582293753991524, 360582255737217877]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641820221259222, 360641820550904296⟩, ⟨(-471065990036077465), (-471064228692912369)⟩, true⟩

def words07 : List Nat := [360582222128139045, 360582193528570704, 360582164936240780, 360582152365009009, 360582132112645909, 360582096616067436, 360582061128483492, 360582041651588033, 360582040826354673, 360582048411747729]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360469346054440389, 360469346384973241⟩, ⟨888744405046900891, 888746173390138903⟩, true⟩

def words08 : List Nat := [360582048411830685, 360582044746315036, 360582055463524731, 360582068813348386, 360582073918759158, 360582073918852336, 360582063105380729, 360582039854528090, 360582016609553371, 360581988485529660]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360273565150327781, 360273565481738596⟩, ⟨2434464423616110656, 2434466198890986154⟩, true⟩

def words09 : List Nat := [360581974210849455, 360581964090482561, 360581953972670597, 360581935708030740, 360581901549455812, 360581863200441976, 360581824861111878, 360581795635988961, 360581764772551083, 360581725760079228]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk078
