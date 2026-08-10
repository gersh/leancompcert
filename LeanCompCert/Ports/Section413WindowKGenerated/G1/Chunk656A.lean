import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497386215954587, 362497449757720192⟩, ⟨(-786729253050610655), (-783913899029264907)⟩, true⟩

def state01 : KState := ⟨⟨362480045521665338, 362480109083604904⟩, ⟨350837782875921519, 353654460409708629⟩, true⟩

def words00 : List Nat := [371285500202854989, 371285500205089884, 371285500065359856, 371285500057041360, 371285500107693077, 371285500109928224, 371285499862227656, 371285499609718067, 371285499356286631, 371285499336011698]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469360945453802, 362469424527519867⟩, ⟨1051904649963850428, 1054722648100603836⟩, true⟩

def words01 : List Nat := [371285499255407693, 371285499222706913, 371285499189272133, 371285499156421660, 371285498847943022, 371285498550402299, 371285498251682315, 371285498185774964, 371285497958755699, 371285497716305308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489686446499192, 362489750048563801⟩, ⟨(-281916889532580859), (-279097578987925283)⟩, true⟩

def words02 : List Nat := [371285497472882097, 371285497441954714, 371285497355022079, 371285497418481240, 371285497423776413, 371285497426032256, 371285497275561918, 371285497259256314, 371285497454766916, 371285497521876902]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486666116697356, 362486729739175757⟩, ⟨(-83624723414064224), (-80804073009313586)⟩, true⟩

def words03 : List Nat := [371285497577561813, 371285497634074094, 371285497921543452, 371285498093951551, 371285498336501465, 371285498579880466, 371285498772785639, 371285498775023097, 371285498717601422, 371285498739145147]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488447588554653, 362488511230964043⟩, ⟨(-200564613952010557), (-197742655174053807)⟩, true⟩

def words04 : List Nat := [371285498936888842, 371285498939128474, 371285498885990171, 371285498833586485, 371285498782238232, 371285498784768867, 371285498852692862, 371285499004288073, 371285499154679579, 371285499202888705]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656A
