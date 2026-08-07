import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590225311480901, 360590284754323770⟩, ⟨(-777228139308483189), (-773418945184814637)⟩, true⟩

def state01 : KState := ⟨⟨360624991425812071, 360625050881626084⟩, ⟨(-4076712075445024753), (-4072901650295203035)⟩, true⟩

def words00 : List Nat := [360582135167165160, 360582135380534299, 360582135704494015, 360582136028710689, 360582136251776298, 360582136477564703, 360582136814052686, 360582137150947937, 360582137576543078, 360582138030109451]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597751117546019, 360597810586475177⟩, ⟨(-1491195587839871696), (-1487383917867069078)⟩, true⟩

def words01 : List Nat := [360582138405997537, 360582138782024716, 360582139104972090, 360582139484671402, 360582139812337944, 360582140140221963, 360582140400439411, 360582140550174200, 360582140716380227, 360582140883060053]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593789198967165, 360593848680847146⟩, ⟨(-1115137598307890848), (-1111324698978185684)⟩, true⟩

def words02 : List Nat := [360582141101648527, 360582141254116950, 360582141345024183, 360582141436070957, 360582141498882544, 360582141633157910, 360582141740122991, 360582141847333815, 360582141898638289, 360582142023390908]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617157169931533, 360617216664781638⟩, ⟨(-3333561722044699400), (-3329747591395317992)⟩, true⟩

def words03 : List Nat := [360582142223543855, 360582142424112361, 360582142735186838, 360582143049123957, 360582143269055618, 360582143489089872, 360582143800454780, 360582144167359472, 360582144537894437, 360582144908728981]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607641424622599, 360607700932605059⟩, ⟨(-2430211777654064079), (-2426396400155975191)⟩, true⟩

def words04 : List Nat := [360582145175159209, 360582145378198583, 360582145622113387, 360582145866427671, 360582146046151224, 360582146165431066, 360582146228823670, 360582146292389324, 360582146466562202, 360582146737281619]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360592233487272821, 360592293008201840⟩, ⟨(-967103377339185935), (-963286770499939151)⟩, true⟩

def words05 : List Nat := [360582147118415264, 360582147499820881, 360582147819357644, 360582148049142718, 360582148203170527, 360582148357540753, 360582148602309290, 360582148766756882, 360582148874821720, 360582148983070471]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601140721900227, 360601200255841104⟩, ⟨(-1812926426598647706), (-1809108584090415730)⟩, true⟩

def words06 : List Nat := [360582149201878728, 360582149522013743, 360582149825481821, 360582150129199720, 360582150337756391, 360582150462450664, 360582150639268227, 360582150816499026, 360582150990605756, 360582151192610324]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596769309339110, 360596828856383545⟩, ⟨(-1397726327668961087), (-1393907240650558437)⟩, true⟩

def words07 : List Nat := [360582151338709268, 360582151484955523, 360582151714169393, 360582152029512826, 360582152287813266, 360582152546354941, 360582152737853524, 360582152901743144, 360582153057375461, 360582153213458639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589221309585086, 360589280869606046⟩, ⟨(-680850537299812155), (-677030217706876669)⟩, true⟩

def words08 : List Nat := [360582153417805286, 360582153511956005, 360582153520903926, 360582153529981724, 360582153531141373, 360582153462687403, 360582153478295443, 360582153509076157, 360582153510302259, 360582153560516692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597121930177919, 360597181503186204⟩, ⟨(-1431403417335614952), (-1427581864012166164)⟩, true⟩

def words09 : List Nat := [360582153669514752, 360582153778909666, 360582153998689610, 360582154108302209, 360582154123067428, 360582154137940814, 360582154139073327, 360582154164945245, 360582154324240333, 360582154483849438]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949
