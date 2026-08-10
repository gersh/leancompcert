import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360503498475006754, 360503500653619441⟩, ⟨1556973011244778176, 1557001616281093110⟩, true⟩

def state01 : KState := ⟨⟨360477500677664070, 360477502858638901⟩, ⟨2061126990116496897, 2061155640989835263⟩, true⟩

def words00 : List Nat := [360583754332325327, 360583748420199134, 360583740761057503, 360583735742573728, 360583730724532929, 360583725037535650, 360583717895199588, 360583709428148871, 360583700961924286, 360583693257453422]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360430046923012673, 360430049106327819⟩, ⟨2982239949838966352, 2982268646149655258⟩, true⟩

def words01 : List Nat := [360583687787027869, 360583681409714442, 360583675033032790, 360583667300864693, 360583658782232397, 360583648465418354, 360583638149594733, 360583630470893119, 360583623885727384, 360583615977911221]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360636760347425160, 360636762533083968⟩, ⟨(-1033196905113669993), (-1033168163277528441)⟩, true⟩

def words02 : List Nat := [360583608070853551, 360583602799676182, 360583599249340905, 360583598334138893, 360583597419015834, 360583593838310620, 360583589911911269, 360583588619896719, 360583588669559716, 360583591406364936]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553055715625468, 360553057903655945⟩, ⟨593828756525750492, 593857544454936664⟩, true⟩

def words03 : List Nat := [360583592227672981, 360583593048925294, 360583596502868742, 360583601680389584, 360583604882034700, 360583608083389720, 360583609211118109, 360583609211366719, 360583607702457263, 360583606131251364]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592338484593864, 360592340674965375⟩, ⟨(-170132275507554958), (-170103442056623522)⟩, true⟩

def words04 : List Nat := [360583605619476946, 360583605619725593, 360583604043229981, 360583601147856808, 360583598252740983, 360583594689905071, 360583594196858249, 360583595264827509, 360583595265051045, 360583595446336687]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194A
