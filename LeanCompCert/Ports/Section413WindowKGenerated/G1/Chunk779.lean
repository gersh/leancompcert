import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503665282644109, 362503756093560528⟩, ⟨(-1448359631548610426), (-1443582565568870776)⟩, true⟩

def state01 : KState := ⟨⟨362488292010727741, 362488382845934642⟩, ⟨(-250739563793658082), (-245960605462936518)⟩, true⟩

def words00 : List Nat := [371285225334221857, 371285225416381086, 371285225553224800, 371285225691492298, 371285225878761387, 371285225881449468, 371285225849290093, 371285225818016139, 371285225859043886, 371285225902685770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469732761382125, 362469823620783498⟩, ⟨1195357081184607430, 1200137924632704574⟩, true⟩

def words01 : List Nat := [371285226049220808, 371285226196865143, 371285226312087668, 371285226314775953, 371285226226808152, 371285226190559588, 371285226181947703, 371285226184636083, 371285225996150555, 371285225801541105]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484752846520065, 362484843730001170⟩, ⟨24945627383734331, 29728347242372831⟩, true⟩

def words02 : List Nat := [371285225605700802, 371285225551559000, 371285225440765885, 371285225448651350, 371285225450734421, 371285225433448453, 371285225225477668, 371285225164425892, 371285225202224127, 371285225205007489]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492226000137997, 362492316908138026⟩, ⟨(-557484425973034137), (-552699795228730411)⟩, true⟩

def words03 : List Nat := [371285225202176709, 371285225168299875, 371285225261149224, 371285225320834327, 371285225381166810, 371285225442541137, 371285225503434538, 371285225506176411, 371285225555111137, 371285225649426582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479874766868637, 362479965698800083⟩, ⟨405244734947045850, 410031231032670682⟩, true⟩

def words04 : List Nat := [371285225867766986, 371285225870456161, 371285225869649348, 371285225869809111, 371285225868953294, 371285225847542893, 371285225802395873, 371285225840144138, 371285225878578677, 371285225881366250]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779
