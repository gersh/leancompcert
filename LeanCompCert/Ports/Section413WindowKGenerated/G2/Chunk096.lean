import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk096

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360444584052054263, 360444584551367816⟩, ⟨1269510078848818113, 1269513328341738167⟩, true⟩

def state01 : KState := ⟨⟨360363905192819690, 360363905693220909⟩, ⟨2044258742887602319, 2044262002827691247⟩, true⟩

def words00 : List Nat := [360576811749497248, 360576808780703646, 360576795088941795, 360576772296869006, 360576749509521678, 360576720209908863, 360576696361972557, 360576675428471254, 360576654499314466, 360576628066043770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360670654079115035, 360670654580610151⟩, ⟨(-905671905740247332), (-905668635282435332)⟩, true⟩

def words01 : List Nat := [360576605932919553, 360576583345994262, 360576560763733589, 360576548959397658, 360576542452830800, 360576526760338110, 360576511071087031, 360576501418375242, 360576510231707934, 360576520017125853]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360632568372104632, 360632568874702132⟩, ⟨(-539836106343736433), (-539832825275477485)⟩, true⟩

def words02 : List Nat := [360576524405355451, 360576525577021294, 360576537502945234, 360576549426424567, 360576551519176558, 360576551519292364, 360576542937858510, 360576528864465958, 360576514793974487, 360576517288649233]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360398321089631055, 360398321593321667⟩, ⟨1717755237857174157, 1717758529457496643⟩, true⟩

def words03 : List Nat := [360576533847517541, 360576550402971865, 360576559485613637, 360576559485729492, 360576557905967957, 360576550343734058, 360576542783035410, 360576539657354528, 360576530798457304, 360576512312145059]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360722801073725927, 360722801578510998⟩, ⟨(-1411911690694447741), (-1411908388538023447)⟩, true⟩

def words04 : List Nat := [360576493829641977, 360576481180371447, 360576477397141299, 360576480861866986, 360576480861973827, 360576475238612230, 360576476498315459, 360576477813084070, 360576489828283327, 360576504988671808]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360627210890495520, 360627211396387822⟩, ⟨(-489084212679280682), (-489080899832643124)⟩, true⟩

def words05 : List Nat := [360576514677281738, 360576524363897202, 360576533352012385, 360576547712344959, 360576559235412932, 360576570756113622, 360576574343003910, 360576576661731642, 360576581903517130, 360576587144257335]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547922341158206, 360547922848143460⟩, ⟨277364574127778241, 277367897538058773⟩, true⟩

def words06 : List Nat := [360576603054695994, 360576608370090298, 360576608370193828, 360576608242048249, 360576608113910350, 360576607766670019, 360576609909305746, 360576612051518762, 360576612051623029, 360576606188116372]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360791540084738337, 360791540592821744⟩, ⟨(-2080175599596073686), (-2080172265561212174)⟩, true⟩

def words07 : List Nat := [360576604616294788, 360576606010131604, 360576610543256446, 360576615497886384, 360576615497994650, 360576611116028428, 360576612984362432, 360576624561450147, 360576646763613793, 360576668961217446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360738369939804457, 360738370448997933⟩, ⟨(-1566352403370610122), (-1566349058584816144)⟩, true⟩

def words08 : List Nat := [360576683006046807, 360576691395664817, 360576704229280421, 360576717060280520, 360576723470335321, 360576725143763596, 360576725143867424, 360576721399196109, 360576724519186361, 360576741199324544]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590960445567371, 360590960955858220⟩, ⟨(-137187723797241114), (-137184368372287006)⟩, true⟩

def words09 : List Nat := [360576759244190271, 360576777285354290, 360576789761844211, 360576797335390027, 360576797568212689, 360576797801016315, 360576808625180192, 360576816779082004, 360576818237348536, 360576819695331235]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk096
