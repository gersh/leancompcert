import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475353300428086, 362475466717554744⟩, ⟨837171835018641905, 843811306833986729⟩, true⟩

def state01 : KState := ⟨⟨362481742429831879, 362481855873866989⟩, ⟨283234883228900076, 289876688147085862⟩, true⟩

def words00 : List Nat := [371285199160403902, 371285199163493644, 371285199102884100, 371285199043461574, 371285198982844891, 371285198964211960, 371285198901943394, 371285198929380572, 371285198931674387, 371285198933354328]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495665267893689, 362495778739213766⟩, ⟨(-924086833404942877), (-917442662470610089)⟩, true⟩

def words01 : List Nat := [371285198991155243, 371285199089099722, 371285199253903579, 371285199256920470, 371285199258119210, 371285199229778214, 371285199252757177, 371285199256082268, 371285199369283899, 371285199494711620]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481952125361449, 362482065623932446⟩, ⟨265125300487243810, 271771834756851478⟩, true⟩

def words02 : List Nat := [371285199614254332, 371285199617271652, 371285199572447595, 371285199560767358, 371285199571650872, 371285199574668377, 371285199437905971, 371285199302315180, 371285199165470233, 371285199162901164]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469677266333446, 362469790792033321⟩, ⟨1329840494726104966, 1336489382023035088⟩, true⟩

def words03 : List Nat := [371285199202631124, 371285199279689280, 371285199343847933, 371285199346873627, 371285199274786986, 371285199207149515, 371285199137925793, 371285199124671200, 371285198960105300, 371285198785831143]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485104276830788, 362485217829524466⟩, ⟨(-8331937103261872), (-1680708223921754)⟩, true⟩

def words04 : List Nat := [371285198610245353, 371285198557687635, 371285198465286936, 371285198487809041, 371285198490144101, 371285198490757939, 371285198371112717, 371285198370466877, 371285198452238035, 371285198455589596]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490355526506431, 362490469106787954⟩, ⟨(-463907510617632158), (-457253888356275550)⟩, true⟩

def words05 : List Nat := [371285198457915028, 371285198422563977, 371285198480015473, 371285198526730393, 371285198612916910, 371285198700236861, 371285198759605076, 371285198762675976, 371285198772322065, 371285198836869947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489267194666986, 362489380801820460⟩, ⟨(-369447963564979552), (-362792009754769254)⟩, true⟩

def words06 : List Nat := [371285199015173996, 371285199093755650, 371285199171685719, 371285199250606792, 371285199317594299, 371285199320920792, 371285199452535908, 371285199587011216, 371285199722174025, 371285199773484326]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499367183519755, 362499480817960443⟩, ⟨(-1245831854391446877), (-1239173532729508301)⟩, true⟩

def words07 : List Nat := [371285199956395752, 371285200140898348, 371285200421780914, 371285200548875351, 371285200659293177, 371285200770661766, 371285200999932112, 371285201164969244, 371285201331620118, 371285201499529802]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494649661084530, 362494763322761754⟩, ⟨(-836466673629359221), (-829805988242596741)⟩, true⟩

def words08 : List Nat := [371285201666465292, 371285201669484331, 371285201779668272, 371285201903711867, 371285202037256571, 371285202061558439, 371285202085163847, 371285202109755912, 371285202240964025, 371285202354594057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481070024713355, 362481183713627381⟩, ⟨342231825008132990, 348894874412152166⟩, true⟩

def words09 : List Nat := [371285202585305844, 371285202817275972, 371285203022661876, 371285203051888119, 371285203120859684, 371285203191324371, 371285203323800974, 371285203326820713, 371285203282638295, 371285203239830286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867
