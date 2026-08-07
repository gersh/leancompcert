import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk538

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471248902259241, 362471290973150754⟩, ⟨736144069389766687, 737673126778105117⟩, true⟩

def state01 : KState := ⟨⟨362467134831763389, 362467176918848123⟩, ⟨957571673437050849, 959101602101769729⟩, true⟩

def words00 : List Nat := [371285002115939587, 371285001994796066, 371285001821061290, 371285001891974522, 371285001893376383, 371285001870987415, 371285001387911396, 371285001135566140, 371285000882287679, 371285000773189357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476317280802355, 362476359384339370⟩, ⟨463436930928118244, 464967744971252548⟩, true⟩

def words01 : List Nat := [371285000443323295, 371285000111202239, 371284999789168407, 371284999791158632, 371284999630818900, 371284999540221999, 371284999448967946, 371284999358242496, 371284998854114918, 371284998695840137]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469658028282664, 362469700147929536⟩, ⟨821888016681675746, 823419697841630018⟩, true⟩

def words02 : List Nat := [371284998687493790, 371284998689305319, 371284998490121590, 371284998165754059, 371284997840681873, 371284997620103184, 371284997226392832, 371284997090228648, 371284996953489593, 371284996817033041]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483272959651706, 362483315095642317⟩, ⟨88964468399556594, 90497029426845190⟩, true⟩

def words03 : List Nat := [371284996594592381, 371284996657261365, 371284996850449010, 371284996852268294, 371284996737735985, 371284996518179753, 371284996297934681, 371284996222006818, 371284995976023811, 371284995946857526]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472923450871871, 362472965603161648⟩, ⟨646142971558191463, 647676410216168479⟩, true⟩

def words04 : List Nat := [371284995916990430, 371284995875549905, 371284995374051339, 371284995119338521, 371284994863734381, 371284994606124440, 371284994115090566, 371284993635548622, 371284993155273796, 371284993020250157]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362462074297079334, 362462116465660564⟩, ⟨1230433546180842385, 1231967862215096431⟩, true⟩

def words05 : List Nat := [371284992798152498, 371284992702034998, 371284992605329451, 371284992484711534, 371284991904277921, 371284991430675186, 371284990956087250, 371284990826426172, 371284990409732894, 371284989987053344]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476283623105141, 362476325807841826⟩, ⟨465130979191688974, 466666165442157732⟩, true⟩

def words06 : List Nat := [371284989563603457, 371284989485209975, 371284989332973632, 371284989403671889, 371284989413154357, 371284989414965095, 371284989053956358, 371284988811422493, 371284988626936240, 371284988628807896]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478107430860091, 362478149632119311⟩, ⟨366905519934401116, 368441596334952144⟩, true⟩

def words07 : List Nat := [371284988469353472, 371284988310634769, 371284988206302787, 371284988208314865, 371284988136469293, 371284988151604121, 371284988166226043, 371284988168048325, 371284987945280519, 371284987820618475]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478013271044812, 362478055488419103⟩, ⟨372026211567310359, 373563156331906581⟩, true⟩

def words08 : List Nat := [371284987912024608, 371284987913834842, 371284987760892642, 371284987608398971, 371284987455237758, 371284987365097185, 371284987276797806, 371284987405995977, 371284987443422808, 371284987445300378]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506693957572800, 362506736191304617⟩, ⟨(-1173745879156840959), (-1172208052803135561)⟩, true⟩

def words09 : List Nat := [371284987533169577, 371284987750598330, 371284988110333005, 371284988112142208, 371284988013401599, 371284987859407951, 371284987892527920, 371284987954224609, 371284988358944995, 371284988764488730]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk538
