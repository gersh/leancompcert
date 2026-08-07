import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk115

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360502286778907736, 360502287508249295⟩, ⟨948265935539274657, 948271618908064997⟩, true⟩

def state01 : KState := ⟨⟨360614962500666868, 360614963231335852⟩, ⟨(-348178178342159105), (-348172479701555677)⟩, true⟩

def words00 : List Nat := [360584738740336804, 360584728877062490, 360584725330335852, 360584727311802312, 360584727311932315, 360584722447530116, 360584716682117824, 360584714857304935, 360584713667358972, 360584716295387494]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603170945429808, 360603171677437527⟩, ⟨(-212573718211234483), (-212568004155035095)⟩, true⟩

def words01 : List Nat := [360584716295513867, 360584715059848084, 360584716329660087, 360584723812629273, 360584725799711080, 360584727786468624, 360584727786594727, 360584723876791469, 360584719593582157, 360584721195347862]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360672026818712221, 360672027552046393⟩, ⟨(-1006113551189950110), (-1006107821846338906)⟩, true⟩

def words02 : List Nat := [360584726930519592, 360584733039145028, 360584734139344450, 360584735239368191, 360584735239486169, 360584738529276427, 360584750242682595, 360584761954084464, 360584767550006125, 360584775117578755]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360722568270821739, 360722569005484447⟩, ⟨(-1589291129693349677), (-1589285385024988221)⟩, true⟩

def words03 : List Nat := [360584784784397547, 360584794449580438, 360584807143586968, 360584815523267188, 360584817486793291, 360584819449992498, 360584826489365931, 360584837365998243, 360584849301263800, 360584861234491900]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360665027945695823, 360665028681703039⟩, ⟨(-926055166135850433), (-926049405945419889)⟩, true⟩

def words04 : List Nat := [360584869406371204, 360584873921851799, 360584874319503120, 360584874717125012, 360584874717243103, 360584873182953809, 360584868696661842, 360584860396189177, 360584852097127159, 360584858185127382]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360464410453925627, 360464411191260077⟩, ⟨1392799037686109790, 1392804813212869392⟩, true⟩

def words05 : List Nat := [360584872568334949, 360584886949079674, 360584897574906074, 360584903803148970, 360584908106932588, 360584912410009989, 360584913139758801, 360584913139899937, 360584906460013542, 360584896036693717]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563612295463053, 360563613034129762⟩, ⟨245419328059604899, 245425118993800579⟩, true⟩

def words06 : List Nat := [360584885615145843, 360584876266538671, 360584871951596432, 360584871801209027, 360584871650835286, 360584865073913001, 360584851094389706, 360584841374576287, 360584831656402405, 360584825231104162]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589402337745914, 360589403077760544⟩, ⟨(-53470760924262726), (-53464954387924626)⟩, true⟩

def words07 : List Nat := [360584823398011867, 360584815241888042, 360584807087145993, 360584803669003755, 360584803669122320, 360584801848989262, 360584800029155631, 360584792673511426, 360584786069448702, 360584786468280541]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360550323272668239, 360550324014014679⟩, ⟨398762674262787092, 398768496228235210⟩, true⟩

def words08 : List Nat := [360584790812217761, 360584790812359260, 360584787769991452, 360584778576312121, 360584769384199009, 360584754840640957, 360584744081647012, 360584740715741915, 360584737350402328, 360584730269081827]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360783089605409318, 360783090348095375⟩, ⟨(-2300027277919484074), (-2300021440421354390)⟩, true⟩

def words09 : List Nat := [360584729034539081, 360584730768102043, 360584739883941137, 360584752398631775, 360584758554416190, 360584764709150806, 360584778242408128, 360584795543070925, 360584812637567376, 360584829729146892]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk115
