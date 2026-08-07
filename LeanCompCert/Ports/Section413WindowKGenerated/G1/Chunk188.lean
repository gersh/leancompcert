import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk188

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362539953399468255, 362539958105944381⟩, ⟨(-1006034665259087030), (-1005974818816450724)⟩, true⟩

def state01 : KState := ⟨⟨362523083651700965, 362523088363421065⟩, ⟨(-688780533579606572), (-688720588523250064)⟩, true⟩

def words00 : List Nat := [371286454485427432, 371286455624629633, 371286459587804257, 371286463550850279, 371286468372505489, 371286469430595446, 371286470488948702, 371286471547389891, 371286473764740237, 371286475711859572]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478623255114195, 362478627972056584⟩, ⟨147979635315058431, 148039678629014005⟩, true⟩

def words01 : List Nat := [371286479490393396, 371286483268753705, 371286487048678130, 371286487845233891, 371286489233404912, 371286490621734506, 371286494316066514, 371286494471774047, 371286494472214253, 371286494054874279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465682938300772, 362465687660448036⟩, ⟨391525209658272696, 391585350954996998⟩, true⟩

def words02 : List Nat := [371286493779310358, 371286493779950120, 371286492514230784, 371286492408468080, 371286492302528748, 371286491724123214, 371286487391051665, 371286485409676469, 371286483483041621, 371286483483653294]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473640995112218, 362473645722557683⟩, ⟨241714959240083134, 241775200328612258⟩, true⟩

def words03 : List Nat := [371286482379748257, 371286481279204831, 371286481257056618, 371286481257697121, 371286481942600750, 371286482715683238, 371286482972826309, 371286482973407975, 371286479481604842, 371286478801131389]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447213814449178, 362447218547079216⟩, ⟨739726826142503192, 739787164934827238⟩, true⟩

def words04 : List Nat := [371286479809553741, 371286479810135475, 371286477752269790, 371286475087242887, 371286472422271483, 371286470619129778, 371286467430041967, 371286466546771833, 371286465663390092, 371286464550524035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362527611023313136, 362527615761198878⟩, ⟨(-776302581877001418), (-776242143987304172)⟩, true⟩

def words05 : List Nat := [371286462469020459, 371286461549335501, 371286461512412270, 371286461512998152, 371286459886299981, 371286457788063179, 371286456078278026, 371286456078929928, 371286457640508237, 371286459823338357]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362453492915776132, 362453497658913098⟩, ⟨621715573938891825, 621776110893293569⟩, true⟩

def words06 : List Nat := [371286462010456255, 371286462011038645, 371286460735641394, 371286461012825871, 371286461013245035, 371286460950626424, 371286457150888659, 371286453222911930, 371286449295120660, 371286448168234418]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362404867677203571, 362404872425601203⟩, ⟨1539797125782695411, 1539857762031910677⟩, true⟩

def words07 : List Nat := [371286447149663697, 371286447877360301, 371286448541427140, 371286448542010038, 371286445472019657, 371286443136678431, 371286440801282925, 371286440770758018, 371286437007916177, 371286432688420690]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362429393292934027, 362429398046548510⟩, ⟨1076854429814233677, 1076915164584826577⟩, true⟩

def words08 : List Nat := [371286428369116397, 371286426463290846, 371286423166646225, 371286421827365759, 371286420488051444, 371286418687228405, 371286415204028268, 371286412142621300, 371286409081234832, 371286407848802869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452509207747826, 362452513966682274⟩, ⟨640032171613454451, 640093006904533799⟩, true⟩

def words09 : List Nat := [371286404831414532, 371286401802552562, 371286398773787045, 371286396908997417, 371286393960145629, 371286391869274539, 371286389778421093, 371286387694422835, 371286383112828185, 371286381321544948]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk188
