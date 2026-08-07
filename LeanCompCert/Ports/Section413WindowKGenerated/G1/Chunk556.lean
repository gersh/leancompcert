import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470110038114435, 362470155090247528⟩, ⟨821544179808173180, 823236327315649016⟩, true⟩

def state01 : KState := ⟨⟨362472954347350128, 362472999416249005⟩, ⟨663385439166077215, 665078518937153947⟩, true⟩

def words00 : List Nat := [371284961234012879, 371284961035181669, 371284960674488122, 371284960637393530, 371284960599744920, 371284960460430718, 371284959889937496, 371284959522516206, 371284959154083541, 371284959109090889]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472537338745673, 362472582424691581⟩, ⟨686588870429595004, 688282898270545962⟩, true⟩

def words01 : List Nat := [371284958895444037, 371284958643591801, 371284958391007510, 371284958379404832, 371284958266704433, 371284958153227992, 371284958039083500, 371284957926202272, 371284957382335950, 371284957162164982]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465771573427126, 362465816676056909⟩, ⟨1063039547103387604, 1064734502989531354⟩, true⟩

def words02 : List Nat := [371284957041090537, 371284957042996931, 371284956936690625, 371284956831856327, 371284956726289048, 371284956698618741, 371284956533212072, 371284956459909037, 371284956386031701, 371284956250081528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493825159801397, 362493870279383808⟩, ⟨(-497706745916404486), (-496010846872653548)⟩, true⟩

def words03 : List Nat := [371284955907306734, 371284955888049330, 371284956168759889, 371284956170632429, 371284956042866436, 371284955863888563, 371284955684140622, 371284955633005507, 371284955632270390, 371284955794617671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362463542872168940, 362463588008660942⟩, ⟨1187300817454901822, 1188997657433824662⟩, true⟩

def words04 : List Nat := [371284955919152859, 371284955921026374, 371284955670252444, 371284955554811154, 371284955438470254, 371284955399787099, 371284954930636639, 371284954446852725, 371284953962305503, 371284953644913123]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362441779252060404, 362441824405391021⟩, ⟨2398600844419124312, 2400298621553806754⟩, true⟩

def words05 : List Nat := [371284953262265888, 371284953023253866, 371284952783642326, 371284952535629746, 371284951857176211, 371284951278341155, 371284950698541703, 371284950253765137, 371284949479583783, 371284948706892168]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474409528227978, 362474454698309844⟩, ⟨582274332001776447, 583973041597590467⟩, true⟩

def words06 : List Nat := [371284947933396147, 371284947482909889, 371284946869933590, 371284946579984765, 371284946289416263, 371284945948148603, 371284945296819375, 371284944968618750, 371284944639480290, 371284944603853182]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476409202953950, 362476454390152616⟩, ⟨470936907539397115, 472636570110324761⟩, true⟩

def words07 : List Nat := [371284944416861277, 371284944120642347, 371284943847482132, 371284943849567870, 371284943715591015, 371284943602588822, 371284943488974390, 371284943350404579, 371284942984402068, 371284942834299713]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470215939868082, 362470261143728871⟩, ⟨815865958401158080, 817566548807961074⟩, true⟩

def words08 : List Nat := [371284942852664404, 371284942854551133, 371284942736453808, 371284942592808264, 371284942448492081, 371284942282296959, 371284941953721837, 371284941912353132, 371284941870340343, 371284941814384428]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483182973495309, 362483228194313213⟩, ⟨93693555222803463, 95395090053980603⟩, true⟩

def words09 : List Nat := [371284941610334145, 371284941670917793, 371284941845391997, 371284941847266490, 371284941592617157, 371284941294720151, 371284941017938374, 371284941020003966, 371284940881680052, 371284940853021543]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556
