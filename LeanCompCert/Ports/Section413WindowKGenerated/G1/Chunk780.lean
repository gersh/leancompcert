import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492506822531546, 362492597875955131⟩, ⟨(-579680922936222057), (-574884953500177769)⟩, true⟩

def state01 : KState := ⟨⟨362482891426009428, 362482982503407568⟩, ⟨170337443027067514, 175135282604551106⟩, true⟩

def words00 : List Nat := [371285227764174145, 371285227766866896, 371285227688764354, 371285227608522749, 371285227527276641, 371285227497420640, 371285227433438379, 371285227485653229, 371285227536929042, 371285227539718356]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500719365043948, 362500810466755457⟩, ⟨(-1220516609516687185), (-1215716873133047587)⟩, true⟩

def words01 : List Nat := [371285227635825295, 371285227762125644, 371285227952221565, 371285227972747777, 371285227974867701, 371285227956590791, 371285228080132684, 371285228143862956, 371285228345411596, 371285228548129279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486484604434819, 362486575730484496⟩, ⟨(-109865489184552220), (-105063853812802052)⟩, true⟩

def words02 : List Nat := [371285228748988354, 371285228813972551, 371285228925933865, 371285229039299023, 371285229200377414, 371285229205151067, 371285229211252630, 371285229218237392, 371285229272754972, 371285229293122258]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482938989654260, 362483030139973887⟩, ⟨166886776739510903, 171690306021357613⟩, true⟩

def words03 : List Nat := [371285229476361201, 371285229660726718, 371285229825352717, 371285229843114337, 371285229910334643, 371285229978911130, 371285230194727705, 371285230197420688, 371285230194664280, 371285230169523110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489106347085385, 362489197521540177⟩, ⟨(-314427151736030983), (-309621738823862301)⟩, true⟩

def words04 : List Nat := [371285230279080837, 371285230335848801, 371285230459702465, 371285230584592894, 371285230657701294, 371285230660394455, 371285230514490651, 371285230473939539, 371285230552155289, 371285230605820663]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491932382212752, 362492023581153038⟩, ⟨(-535000929228333759), (-530193605097962061)⟩, true⟩

def words05 : List Nat := [371285230658675512, 371285230712434640, 371285230908825330, 371285231024247139, 371285231173709320, 371285231324243168, 371285231434140944, 371285231436836537, 371285231448649827, 371285231538966826]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483365920345629, 362483457143287103⟩, ⟨133775884126327706, 138585081911888980⟩, true⟩

def words06 : List Nat := [371285231777599796, 371285231840569065, 371285231902870962, 371285231966177560, 371285232059225935, 371285232071998048, 371285232141281426, 371285232211624596, 371285232279242804, 371285232282033253]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501328441369289, 362501419688728656⟩, ⟨(-1268698353231376541), (-1263887249022260407)⟩, true⟩

def words07 : List Nat := [371285232278423890, 371285232298936449, 371285232458474350, 371285232461168697, 371285232419801453, 371285232348634594, 371285232349555989, 371285232395971042, 371285232605115092, 371285232815494166]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478378172947249, 362478469444584679⟩, ⟨523347393278273449, 528160393242028389⟩, true⟩

def words08 : List Nat := [371285233003967535, 371285233006661880, 371285233099330329, 371285233225492246, 371285233327147034, 371285233329841520, 371285233213062106, 371285233097238255, 371285232980309469, 371285232927658595]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467561679120016, 362467652975035800⟩, ⟨1368106509398018681, 1372921405383759335⟩, true⟩

def words09 : List Nat := [371285232864623290, 371285232889311798, 371285232912261350, 371285232914956293, 371285232719293444, 371285232575210183, 371285232429698539, 371285232407272647, 371285232216370365, 371285231994310881]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780
