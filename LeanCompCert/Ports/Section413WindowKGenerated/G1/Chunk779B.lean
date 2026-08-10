import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779A

def state06 : KState := ⟨⟨362485546693637090, 362485637649940091⟩, ⟨(-36856045467170615), (-32067649500760615)⟩, true⟩

def words05 : List Nat := [371285225912695527, 371285226012997173, 371285226256482773, 371285226281574401, 371285226283655947, 371285226282337581, 371285226327532296, 371285226330525011, 371285226312241146, 371285226320563855]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486079331937831, 362486170312503933⟩, ⟨(-78431785901422482), (-73641498259614848)⟩, true⟩

def words06 : List Nat := [371285226325253241, 371285226327950365, 371285226164041762, 371285226141256188, 371285226133766816, 371285226136503729, 371285226018350019, 371285225900270257, 371285225824394469, 371285225839581185]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480312328656325, 362480403333466084⟩, ⟨371312463659506707, 376104641700299051⟩, true⟩

def words07 : List Nat := [371285225999102441, 371285226159690246, 371285226289964610, 371285226292667987, 371285226285299824, 371285226308484759, 371285226494577161, 371285226497267893, 371285226483338147, 371285226424536876]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487972284970664, 362488063313839241⟩, ⟨(-226016427642816204), (-221222373370603828)⟩, true⟩

def words08 : List Nat := [371285226425057747, 371285226428024336, 371285226569041757, 371285226723762661, 371285226852872370, 371285226855563390, 371285226765355657, 371285226716064524, 371285226763100249, 371285226802275464]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492506822531546, 362492597875955131⟩, ⟨(-579680922936222057), (-574884953500177769)⟩, true⟩

def words09 : List Nat := [371285226840702597, 371285226880061659, 371285227034872192, 371285227130899002, 371285227261344835, 371285227392801480, 371285227523412278, 371285227526104400, 371285227552646193, 371285227650528532]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779B
