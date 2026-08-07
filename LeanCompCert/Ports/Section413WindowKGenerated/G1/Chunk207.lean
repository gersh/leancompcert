import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk207

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362406671972026340, 362406677726020195⟩, ⟨1615146743178258942, 1615227295429708656⟩, true⟩

def state01 : KState := ⟨⟨362413627861424349, 362413633621155972⟩, ⟨1471185878276735338, 1471266549329039624⟩, true⟩

def words00 : List Nat := [371284704261186582, 371284702444290261, 371284698546145475, 371284694413847853, 371284690281695284, 371284686334859989, 371284681796432306, 371284679579994405, 371284677363566518, 371284674980370315]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458723112244501, 362458728877809374⟩, ⟨536930401948542528, 537011193837237052⟩, true⟩

def words01 : List Nat := [371284671550680999, 371284670113987753, 371284668677106117, 371284667441446707, 371284663106779870, 371284658373214181, 371284653639850286, 371284651226332937, 371284647656631424, 371284646406469473]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362401713218689913, 362401718990064683⟩, ⟨1718349254169814104, 1718430166469923464⟩, true⟩

def words02 : List Nat := [371284645156165952, 371284643915303307, 371284640465318600, 371284637797929609, 371284635130483453, 371284633149592468, 371284628500058850, 371284623360632375, 371284618221435942, 371284614801278862]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362380986197682915, 362380991974861438⟩, ⟨2148395768989729291, 2148476801630509211⟩, true⟩

def words03 : List Nat := [371284610803076632, 371284609121954135, 371284607440782540, 371284605769766231, 371284602166436712, 371284598401920086, 371284594637416829, 371284592836222461, 371284587943167481, 371284582948903411]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362455526933230256, 362455532716193105⟩, ⟨602036777099044685, 602117929735916225⟩, true⟩

def words04 : List Nat := [371284577954846860, 371284573941702937, 371284568766083536, 371284565904730327, 371284563043451690, 371284559840519906, 371284555179027510, 371284552831032817, 371284550482920213, 371284550447746644]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362455072008844436, 362455077797688063⟩, ⟨611563275680403705, 611644550373757099⟩, true⟩

def words05 : List Nat := [371284549049852014, 371284547662148845, 371284547197812002, 371284547198529680, 371284546972070375, 371284546782283104, 371284546592307352, 371284545592983373, 371284541863089851, 371284540444623216]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362438956398932294, 362438962193539735⟩, ⟨946323930287618941, 946405324667260095⟩, true⟩

def words06 : List Nat := [371284539139820292, 371284539140477556, 371284537327825952, 371284535510263606, 371284533692634895, 371284532591759271, 371284530330154104, 371284529784786896, 371284529239250190, 371284528169691265]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362540025592234720, 362540031392678137⟩, ⟨(-1153241904382360740), (-1153160388759721556)⟩, true⟩

def words07 : List Nat := [371284526090517795, 371284526205397274, 371284528627348347, 371284529598633149, 371284530222244342, 371284530846013879, 371284533481867014, 371284534958157629, 371284537629265512, 371284540300393853]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499356148498398, 362499361954791943⟩, ⟨(-308183377318204745), (-308101740100529425)⟩, true⟩

def words08 : List Nat := [371284542957041480, 371284542957688430, 371284543088471420, 371284543642571057, 371284544914228036, 371284544914876431, 371284543807289776, 371284542519136581, 371284542245511161, 371284542959067807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362441836170240871, 362441841982358950⟩, ⟨888153976416637707, 888235734755903797⟩, true⟩

def words09 : List Nat := [371284545125770464, 371284547292532468, 371284549237063202, 371284549237710740, 371284548629833267, 371284548685448807, 371284549717271940, 371284549717919284, 371284547675871540, 371284545623452984]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk207
