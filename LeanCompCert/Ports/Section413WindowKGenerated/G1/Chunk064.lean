import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk064

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362591144235888829, 362591144729947505⟩, ⟨(-708807902442371774), (-708805760800057406)⟩, true⟩

def state01 : KState := ⟨⟨362569940627128884, 362569941122795855⟩, ⟨(-572194861069968428), (-572192709126267438)⟩, true⟩

def words00 : List Nat := [371280446247502572, 371280472889589654, 371280516367935607, 371280559832776043, 371280596683970223, 371280601133983663, 371280623729240122, 371280646317541164, 371280675489360654, 371280689413370451]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362450129804021592, 362450130301327639⟩, ⟨196850108652791039, 196852271111519177⟩, true⟩

def words01 : List Nat := [371280703196656903, 371280716975707005, 371280741501117956, 371280753966154992, 371280773581961838, 371280793191725857, 371280811441408693, 371280811441588950, 371280797425443067, 371280792648852798]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362543006759232960, 362543007258145680⟩, ⟨(-399381472128444671), (-399379299346506189)⟩, true⟩

def words02 : List Nat := [371280807358711080, 371280808893818493, 371280810318730684, 371280811743262864, 371280820028308610, 371280820736704858, 371280845660311409, 371280870576235857, 371280895391808745, 371280905050192562]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362654056910572633, 362654057411120604⟩, ⟨(-1114116561857887737), (-1114114378553185527)⟩, true⟩

def words03 : List Nat := [371280933310022935, 371280961561162539, 371280999457241214, 371281005248420079, 371281005628245979, 371281006008005589, 371281023328161005, 371281031416294772, 371281058283808154, 371281085143063907]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362540050135897727, 362540050638076935⟩, ⟨(-380016811085157766), (-380014617266959810)⟩, true⟩

def words04 : List Nat := [371281111826819178, 371281111827000022, 371281115805066343, 371281125112368783, 371281141523748808, 371281141523930910, 371281137153664099, 371281127975244928, 371281133642945687, 371281142776153674]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478791208621320, 362478791712427518⟩, ⟨16367195067950945, 16369399388725343⟩, true⟩

def words05 : List Nat := [371281175915285123, 371281209044217247, 371281241624757127, 371281254647077601, 371281274748552348, 371281294843891107, 371281326382729440, 371281326382910620, 371281326067293711, 371281325675181191]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362509057986674401, 362509058492106685⟩, ⟨(-179365513790120758), (-179363298956598676)⟩, true⟩

def words06 : List Nat := [371281329768447851, 371281329768649076, 371281331855123615, 371281341174132747, 371281346635477586, 371281346635659119, 371281326032255765, 371281321461627724, 371281336189143552, 371281340473414582]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463170996359549, 362463171503449557⟩, ⟨118352985838692482, 118355211405931310⟩, true⟩

def words07 : List Nat := [371281344642787427, 371281348810933446, 371281376824549047, 371281396446120359, 371281415198236150, 371281433944626861, 371281449354303255, 371281449354485207, 371281439015399195, 371281436196567757]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493091429284441, 362493091937997254⟩, ⟨(-75176181916425364), (-75173945824864596)⟩, true⟩

def words08 : List Nat := [371281454369245693, 371281456008450463, 371281457533667001, 371281459058472758, 371281467600722360, 371281467600922978, 371281483020023510, 371281498450731561, 371281508895307481, 371281510679974629]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362764179953665951, 362764180464026467⟩, ⟨(-1835712772205786959), (-1835710525412283207)⟩, true⟩

def words09 : List Nat := [371281536184925343, 371281561682111541, 371281605166658813, 371281625303941080, 371281641678597502, 371281658048275908, 371281693612200689, 371281720004333141, 371281763459912684, 371281806902203320]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk064
