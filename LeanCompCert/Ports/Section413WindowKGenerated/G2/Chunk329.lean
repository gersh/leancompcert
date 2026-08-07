import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk329

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599028503556672, 360599035064736977⟩, ⟨(-583096717447556636), (-582950758767803972)⟩, true⟩

def state01 : KState := ⟨⟨360548536514130065, 360548543079487989⟩, ⟨1078003844747703844, 1078149940892658798⟩, true⟩

def words00 : List Nat := [360581316735634073, 360581316565286862, 360581315473511867, 360581314649233641, 360581313824885055, 360581312767897590, 360581310789689079, 360581308098381677, 360581305407153008, 360581303636792537]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537425399131676, 360537431968624870⟩, ⟨1443872461700554747, 1444018693957919893⟩, true⟩

def words01 : List Nat := [360581302641718928, 360581302567297465, 360581302492833191, 360581301796070905, 360581301129235996, 360581299996487170, 360581298863676468, 360581298651287765, 360581297781043085, 360581296449000263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360524999455815169, 360525006029461881⟩, ⟨1852978223475500972, 1853124592486788768⟩, true⟩

def words02 : List Nat := [360581295116945264, 360581293760545414, 360581292994435544, 360581291996302820, 360581290998196916, 360581289213628664, 360581286836797298, 360581284863393783, 360581282889975847, 360581280690636700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539126022483135, 360539132600313975⟩, ⟨1387705496977938459, 1387852003793210461⟩, true⟩

def words03 : List Nat := [360581278982165948, 360581276810787304, 360581274639456537, 360581273387774628, 360581272836107073, 360581271645561904, 360581270455040475, 360581268803202392, 360581266605205612, 360581265326597922]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572484813621283, 360572491395598409⟩, ⟨288818209687528596, 288964853101798252⟩, true⟩

def words04 : List Nat := [360581264047917373, 360581263728550576, 360581263728942233, 360581263248095831, 360581262767208988, 360581261666501680, 360581261481316680, 360581261695266787, 360581261695668894, 360581261193871605]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360615947802685898, 360615954388811758⟩, ⟨(-1143569817178194266), (-1143423037042403180)⟩, true⟩

def words05 : List Nat := [360581261343408568, 360581261759195570, 360581262723650036, 360581262769555825, 360581262769963101, 360581262028151426, 360581261462251489, 360581262102523323, 360581263155436707, 360581264208385121]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556358751514040, 360556365341834290⟩, ⟨820407115167945847, 820554033571000033⟩, true⟩

def words06 : List Nat := [360581264800559244, 360581264800999028, 360581264474868386, 360581263744111020, 360581263013282295, 360581261817081891, 360581260036714072, 360581257465468205, 360581254894292199, 360581253240941691]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360508730012621368, 360508736607081003⟩, ⟨2391092783601343969, 2391239838501173929⟩, true⟩

def words07 : List Nat := [360581252649118992, 360581252812212671, 360581252812604956, 360581252393593228, 360581251057022173, 360581249482248745, 360581247907443902, 360581246299305103, 360581244561338072, 360581242363251445]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360541513794785782, 360541520393397457⟩, ⟨1309734439585763669, 1309881631440824995⟩, true⟩

def words08 : List Nat := [360581240165199343, 360581237842331912, 360581236121972948, 360581235318707775, 360581234515451840, 360581232929454930, 360581230426534872, 360581228840625200, 360581227254685284, 360581225808112245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571107841004119, 360571114443814654⟩, ⟨333184080772169759, 333331411167925127⟩, true⟩

def words09 : List Nat := [360581224604988489, 360581222693211800, 360581220781466834, 360581219786411521, 360581219404184664, 360581218789349724, 360581218174504997, 360581216923231066, 360581215701261319, 360581215395668228]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk329
