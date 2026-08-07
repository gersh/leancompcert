import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk157

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602636105405141, 360602637504903380⟩, ⟨(-348918598335817265), (-348903721823986907)⟩, true⟩

def state01 : KState := ⟨⟨360640081930495517, 360640083331858453⟩, ⟨(-937074934578995722), (-937060028782256816)⟩, true⟩

def words00 : List Nat := [360580417021867466, 360580420349456744, 360580425891062217, 360580431432000450, 360580433436248968, 360580433436446275, 360580432323747055, 360580433233005109, 360580435971451770, 360580439768190816]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564110096012276, 360564111499253518⟩, ⟨256926221992761354, 256941157307073808⟩, true⟩

def words01 : List Nat := [360580441518793682, 360580443269195300, 360580446687434994, 360580452515145535, 360580455553147940, 360580458590793148, 360580458954864574, 360580458955062194, 360580457396179181, 360580456356588574]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630018307403183, 360630019712506562⟩, ⟨(-779580759071921827), (-779565794475517087)⟩, true⟩

def words02 : List Nat := [360580457120094668, 360580459050289217, 360580459050466756, 360580458960385559, 360580458870284368, 360580455777382569, 360580457721759304, 360580460710036632, 360580460710215614, 360580463689718722]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360808506921671804, 360808508328637449⟩, ⟨(-3588287075999261280), (-3588272082100029718)⟩, true⟩

def words03 : List Nat := [360580470870926046, 360580478051280674, 360580489261184499, 360580496460682921, 360580500245776018, 360580504030406975, 360580511843823086, 360580522301073114, 360580536785732895, 360580551268596789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360703362281387699, 360703363690240522⟩, ⟨(-1933509701230881726), (-1933494677618645904)⟩, true⟩

def words04 : List Nat := [360580562620478088, 360580572720620769, 360580581047217213, 360580589372810167, 360580595802649998, 360580598227996615, 360580598228172937, 360580598184784361, 360580602123176407, 360580609917297938]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360477497301650458, 360477498712365905⟩, ⟨1625335776267086385, 1625350829225051909⟩, true⟩

def words05 : List Nat := [360580619376352047, 360580628834243927, 360580635743464902, 360580638651163500, 360580639225455773, 360580639799727994, 360580640226733668, 360580640226931632, 360580636654240271, 360580630110159373]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590136170839684, 360590137583423503⟩, ⟨(-150308922886891182), (-150293840474033772)⟩, true⟩

def words06 : List Nat := [360580623566864407, 360580621333813467, 360580622141368184, 360580622948860498, 360580622949042983, 360580620369477141, 360580613792844361, 360580611234026887, 360580608675474937, 360580607823707947]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360661145447953978, 360661146862426516⟩, ⟨(-1270639556951267883), (-1270624444743932629)⟩, true⟩

def words07 : List Nat := [360580607823887439, 360580605341901064, 360580604392873343, 360580609035810521, 360580612612166761, 360580616188102411, 360580617765860728, 360580620564762746, 360580625667983963, 360580630770623466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360657598242033869, 360657599658372541⟩, ⟨(-1214698418024289302), (-1214683276359821760)⟩, true⟩

def words08 : List Nat := [360580638236668097, 360580644664069943, 360580649055694874, 360580653446785053, 360580653669151503, 360580655929019250, 360580662194470208, 360580668459165334, 360580672281577068, 360580677153378569]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360721637973251531, 360721639391465951⟩, ⟨(-2226075485484650069), (-2226060314193018131)⟩, true⟩

def words09 : List Nat := [360580686029286992, 360580694904132834, 360580705028207857, 360580712874774248, 360580717291363267, 360580721707407351, 360580730124609028, 360580740580147230, 360580749497957009, 360580758414680114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk157
